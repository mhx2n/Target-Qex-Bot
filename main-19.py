#!/usr/bin/env python3
# -*- coding: utf-8 -*-

from __future__ import annotations

import asyncio
import csv
import html
import io
import json
import logging
from logging.handlers import RotatingFileHandler
import os
import re
import sqlite3
import tempfile
import threading
import sys
import time
import uuid
from glob import glob
from collections import defaultdict
from contextlib import closing, suppress
from dataclasses import dataclass
from datetime import datetime, timezone
from http.server import BaseHTTPRequestHandler, HTTPServer
from pathlib import Path
from typing import Any, Dict, Iterable, List, Optional, Tuple

import psutil
from PIL import Image, ImageDraw, ImageFont
from telegram import (
    InlineKeyboardButton,
    InlineKeyboardMarkup,
    InputFile,
    LinkPreviewOptions,
    Message,
    Poll,
    Update,
)
from telegram.constants import ChatAction, ChatMemberStatus, ParseMode
from telegram.error import BadRequest, Forbidden, TelegramError
from telegram.ext import (
    Application,
    ApplicationBuilder,
    CallbackQueryHandler,
    ContextTypes,
    MessageHandler,
    PollAnswerHandler,
    ChatMemberHandler,
    filters,
)
from zoneinfo import ZoneInfo


# ============================================================
# Configuration
# ============================================================

BASE_DIR = Path(__file__).resolve().parent
DATA_DIR = BASE_DIR / "data"
LOG_DIR = BASE_DIR / "logs"
TEMP_DIR = BASE_DIR / "temp"
FONTS_DIR = BASE_DIR / "fonts"
for _p in (DATA_DIR, LOG_DIR, TEMP_DIR, FONTS_DIR):
    _p.mkdir(parents=True, exist_ok=True)

DB_PATH = DATA_DIR / "quiz_exam_bot.sqlite3"
LOG_FILE = LOG_DIR / "bot.log"
START_TS = time.time()


def env_bool(key: str, default: bool = False) -> bool:
    raw = os.getenv(key)
    if raw is None:
        return default
    return str(raw).strip().lower() in {"1", "true", "yes", "on"}


@dataclass(slots=True)
class Config:
    bot_token: str
    owner_ids: Tuple[int, ...]
    required_channel: str
    brand_name: str
    timezone_name: str
    port: int
    retention_hours: int
    scoreboard_top_n: int
    countdown_seconds: int
    delete_delay_seconds: int
    log_level: str



def parse_owner_ids(raw: str) -> Tuple[int, ...]:
    values: List[int] = []
    for part in (raw or "").replace(" ", "").split(","):
        if not part:
            continue
        try:
            value = int(part)
        except ValueError:
            continue
        if value > 0 and value not in values:
            values.append(value)
    return tuple(values)


_OWNER_ENV_RAW = os.getenv("OWNER_IDS", "").strip() or os.getenv("OWNER_ID", "").strip()

CONFIG = Config(
    bot_token=os.getenv("BOT_TOKEN", "").strip(),
    owner_ids=parse_owner_ids(_OWNER_ENV_RAW),
    required_channel=os.getenv("REQUIRED_CHANNEL", "@FX_Ur_Target").strip(),
    brand_name=os.getenv("BOT_BRAND", "Target Exam Robot").strip() or "Target Exam Robot",
    timezone_name=os.getenv("TZ", "Asia/Dhaka"),
    port=int(os.getenv("PORT", "10000")),
    retention_hours=int(os.getenv("RESULT_RETENTION_HOURS", "24")),
    scoreboard_top_n=int(os.getenv("SCOREBOARD_TOP_N", "10")),
    countdown_seconds=int(os.getenv("COUNTDOWN_SECONDS", "5")),
    delete_delay_seconds=int(os.getenv("AUTO_DELETE_CONTROL_AFTER", "180")),
    log_level=os.getenv("LOG_LEVEL", "INFO").upper(),
)

if not CONFIG.bot_token:
    raise SystemExit("BOT_TOKEN is required.")
if not CONFIG.owner_ids:
    raise SystemExit("OWNER_IDS is required.")

TZ = ZoneInfo(CONFIG.timezone_name)
OWNER_SET = set(CONFIG.owner_ids)


# ============================================================
# Logging
# ============================================================

logging.basicConfig(
    level=getattr(logging, CONFIG.log_level, logging.INFO),
    format="%(asctime)s | %(levelname)s | %(name)s | %(message)s",
    handlers=[
        logging.StreamHandler(),
        RotatingFileHandler(LOG_FILE, maxBytes=2 * 1024 * 1024, backupCount=2, encoding="utf-8"),
    ],
)
logger = logging.getLogger("advanced_quiz_exam_bot")


# ============================================================
# Utilities
# ============================================================


def now_ts() -> int:
    return int(time.time())



def now_local() -> datetime:
    return datetime.now(TZ)



def fmt_dt(ts: Optional[int]) -> str:
    if not ts:
        return "—"
    return datetime.fromtimestamp(int(ts), TZ).strftime("%d %b %Y • %I:%M:%S %p")



def fmt_duration(seconds: float) -> str:
    seconds = int(max(0, seconds))
    days, rem = divmod(seconds, 86400)
    hours, rem = divmod(rem, 3600)
    minutes, sec = divmod(rem, 60)
    parts: List[str] = []
    if days:
        parts.append(f"{days}d")
    if hours:
        parts.append(f"{hours}h")
    if minutes:
        parts.append(f"{minutes}m")
    parts.append(f"{sec}s")
    return " ".join(parts)



def fmt_score(score: float) -> str:
    if abs(score - round(score)) < 1e-9:
        return f"{int(round(score))}.00"
    return f"{score:.2f}"



def html_escape(value: Any) -> str:
    return html.escape(str(value or ""))



def jdump(obj: Any) -> str:
    return json.dumps(obj, ensure_ascii=False)



def jload(raw: Any, default: Any = None) -> Any:
    if raw in (None, "", b""):
        return default
    try:
        return json.loads(raw)
    except Exception:
        return default



def short_uuid() -> str:
    return uuid.uuid4().hex[:8].upper()



def chunked(items: List[Any], size: int) -> Iterable[List[Any]]:
    for i in range(0, len(items), size):
        yield items[i:i + size]



def extract_command(text: str, bot_username: str) -> Tuple[Optional[str], str]:
    if not text:
        return None, ""
    text = text.strip()
    m = re.match(r"^([/.])([A-Za-z][A-Za-z0-9_]*)(?:@([A-Za-z0-9_]+))?(?:\s+(.*))?$", text, flags=re.S)
    if not m:
        return None, ""
    command = (m.group(2) or "").lower()
    target = (m.group(3) or "").lower()
    args = (m.group(4) or "").strip()
    if target and target != bot_username.lower():
        return None, ""
    return command, args



def parse_schedule_input(raw: str) -> Optional[int]:
    raw = (raw or "").strip()
    if not raw:
        return None
    for fmt in ("%Y-%m-%d %H:%M", "%d-%m-%Y %H:%M", "%d/%m/%Y %H:%M"):
        with suppress(ValueError):
            dt = datetime.strptime(raw, fmt).replace(tzinfo=TZ)
            return int(dt.timestamp())
    return None



def get_message_link(chat_id: int, message_id: int, username: Optional[str]) -> Optional[str]:
    if username:
        username = username.lstrip("@")
        return f"https://t.me/{username}/{message_id}"
    chat_s = str(chat_id)
    if chat_s.startswith("-100"):
        return f"https://t.me/c/{chat_s[4:]}/{message_id}"
    return None



def choose_name(username: Optional[str], first_name: Optional[str], last_name: Optional[str]) -> str:
    full = " ".join(x for x in [first_name, last_name] if x).strip()
    if full:
        return full
    if username:
        return f"@{username}"
    return "Unknown User"


def split_user_labels(display_name: Optional[str], username: Optional[str], fallback_user_id: Optional[int] = None) -> Tuple[str, str]:
    main = (display_name or "").strip()
    uname = (username or "").strip()
    if uname and not uname.startswith("@"):
        uname = f"@{uname}"
    if not main:
        main = uname or (str(fallback_user_id) if fallback_user_id else "Unknown User")
        uname = ""
    if uname and uname == main:
        uname = ""
    return main, uname


def user_has_staff_access(user_id: int) -> bool:
    return is_bot_admin(user_id)


def pdf_safe_filename(text: str) -> str:
    cleaned = re.sub(r"[^A-Za-z0-9._-]+", "_", (text or "report").strip())
    cleaned = cleaned.strip("._") or "report"
    return cleaned[:80]


def warning_text() -> str:
    return (
        "⛔ এই bot-এর admin/owner permission আপনার নেই।\n"
        "Permission ছাড়া panel, draft, start/stop, schedule, logs, broadcast ব্যবহার করা যাবে না।\n"
        "Owner যদি access দেয়, তখনই advanced feature ব্যবহার করতে পারবেন।"
    )



def health_server(port: int) -> None:
    class Handler(BaseHTTPRequestHandler):
        def do_GET(self):
            self.send_response(200)
            self.send_header("Content-Type", "text/plain; charset=utf-8")
            self.end_headers()
            self.wfile.write(b"OK")

        def log_message(self, fmt, *args):
            return

    server = HTTPServer(("0.0.0.0", port), Handler)
    server.serve_forever()


# ============================================================
# Database
# ============================================================

class DB:
    def __init__(self, path: Path):
        self.path = path
        self._init_db()

    def connect(self) -> sqlite3.Connection:
        conn = sqlite3.connect(self.path)
        conn.row_factory = sqlite3.Row
        conn.execute("PRAGMA journal_mode=WAL")
        conn.execute("PRAGMA synchronous=NORMAL")
        conn.execute("PRAGMA foreign_keys=ON")
        return conn

    def _init_db(self) -> None:
        with closing(self.connect()) as conn:
            conn.executescript(
                """
                CREATE TABLE IF NOT EXISTS bot_admins (
                    user_id INTEGER PRIMARY KEY,
                    added_by INTEGER NOT NULL,
                    added_at INTEGER NOT NULL
                );

                CREATE TABLE IF NOT EXISTS known_users (
                    user_id INTEGER PRIMARY KEY,
                    username TEXT,
                    first_name TEXT,
                    last_name TEXT,
                    started INTEGER NOT NULL DEFAULT 0,
                    last_seen INTEGER NOT NULL DEFAULT 0
                );

                CREATE TABLE IF NOT EXISTS known_chats (
                    chat_id INTEGER PRIMARY KEY,
                    title TEXT,
                    username TEXT,
                    chat_type TEXT,
                    active INTEGER NOT NULL DEFAULT 1,
                    last_seen INTEGER NOT NULL DEFAULT 0
                );

                CREATE TABLE IF NOT EXISTS audit_logs (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    actor_id INTEGER NOT NULL,
                    action TEXT NOT NULL,
                    target TEXT,
                    details TEXT,
                    created_at INTEGER NOT NULL
                );

                CREATE TABLE IF NOT EXISTS drafts (
                    id TEXT PRIMARY KEY,
                    owner_id INTEGER NOT NULL,
                    title TEXT NOT NULL,
                    question_time INTEGER NOT NULL,
                    negative_mark REAL NOT NULL,
                    status TEXT NOT NULL,
                    created_at INTEGER NOT NULL,
                    updated_at INTEGER NOT NULL
                );

                CREATE TABLE IF NOT EXISTS draft_questions (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    draft_id TEXT NOT NULL,
                    q_no INTEGER NOT NULL,
                    question TEXT NOT NULL,
                    options TEXT NOT NULL,
                    correct_option INTEGER NOT NULL,
                    explanation TEXT,
                    src TEXT,
                    FOREIGN KEY(draft_id) REFERENCES drafts(id) ON DELETE CASCADE
                );

                CREATE TABLE IF NOT EXISTS active_drafts (
                    user_id INTEGER PRIMARY KEY,
                    draft_id TEXT NOT NULL,
                    updated_at INTEGER NOT NULL,
                    FOREIGN KEY(draft_id) REFERENCES drafts(id) ON DELETE CASCADE
                );

                CREATE TABLE IF NOT EXISTS user_state (
                    user_id INTEGER PRIMARY KEY,
                    state TEXT NOT NULL,
                    payload TEXT,
                    updated_at INTEGER NOT NULL
                );

                CREATE TABLE IF NOT EXISTS group_bindings (
                    chat_id INTEGER PRIMARY KEY,
                    draft_id TEXT NOT NULL,
                    created_by INTEGER NOT NULL,
                    updated_at INTEGER NOT NULL,
                    FOREIGN KEY(draft_id) REFERENCES drafts(id) ON DELETE CASCADE
                );

                CREATE TABLE IF NOT EXISTS sessions (
                    id TEXT PRIMARY KEY,
                    chat_id INTEGER NOT NULL,
                    draft_id TEXT NOT NULL,
                    title TEXT NOT NULL,
                    question_time INTEGER NOT NULL,
                    negative_mark REAL NOT NULL,
                    total_questions INTEGER NOT NULL,
                    current_index INTEGER NOT NULL DEFAULT 0,
                    status TEXT NOT NULL,
                    started_at INTEGER NOT NULL,
                    ended_at INTEGER,
                    created_by INTEGER NOT NULL,
                    status_message_id INTEGER,
                    countdown_message_id INTEGER,
                    active_poll_id TEXT,
                    active_poll_message_id INTEGER
                );

                CREATE TABLE IF NOT EXISTS session_questions (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    session_id TEXT NOT NULL,
                    q_no INTEGER NOT NULL,
                    question TEXT NOT NULL,
                    options TEXT NOT NULL,
                    correct_option INTEGER NOT NULL,
                    explanation TEXT,
                    poll_id TEXT,
                    message_id INTEGER,
                    open_ts INTEGER,
                    close_ts INTEGER,
                    UNIQUE(session_id, q_no),
                    FOREIGN KEY(session_id) REFERENCES sessions(id) ON DELETE CASCADE
                );

                CREATE TABLE IF NOT EXISTS participants (
                    session_id TEXT NOT NULL,
                    user_id INTEGER NOT NULL,
                    username TEXT,
                    display_name TEXT,
                    eligible INTEGER NOT NULL DEFAULT 1,
                    correct_count INTEGER NOT NULL DEFAULT 0,
                    wrong_count INTEGER NOT NULL DEFAULT 0,
                    score REAL NOT NULL DEFAULT 0,
                    last_answer_at INTEGER NOT NULL DEFAULT 0,
                    PRIMARY KEY(session_id, user_id),
                    FOREIGN KEY(session_id) REFERENCES sessions(id) ON DELETE CASCADE
                );

                CREATE TABLE IF NOT EXISTS answers (
                    session_id TEXT NOT NULL,
                    q_no INTEGER NOT NULL,
                    user_id INTEGER NOT NULL,
                    selected_option INTEGER NOT NULL,
                    is_correct INTEGER NOT NULL,
                    answered_at INTEGER NOT NULL,
                    PRIMARY KEY(session_id, q_no, user_id),
                    FOREIGN KEY(session_id) REFERENCES sessions(id) ON DELETE CASCADE
                );

                CREATE TABLE IF NOT EXISTS schedules (
                    id TEXT PRIMARY KEY,
                    chat_id INTEGER NOT NULL,
                    draft_id TEXT NOT NULL,
                    run_at INTEGER NOT NULL,
                    created_by INTEGER NOT NULL,
                    status TEXT NOT NULL,
                    created_at INTEGER NOT NULL
                );

                CREATE TABLE IF NOT EXISTS delete_queue (
                    kind TEXT NOT NULL,
                    ref_id TEXT PRIMARY KEY,
                    delete_after INTEGER NOT NULL
                );

                CREATE INDEX IF NOT EXISTS idx_draft_questions_draft ON draft_questions(draft_id, q_no);
                CREATE INDEX IF NOT EXISTS idx_sessions_chat_status ON sessions(chat_id, status);
                CREATE INDEX IF NOT EXISTS idx_session_questions_poll ON session_questions(poll_id);
                CREATE TABLE IF NOT EXISTS practice_links (
                    draft_id TEXT PRIMARY KEY,
                    token TEXT NOT NULL UNIQUE,
                    max_attempts INTEGER NOT NULL DEFAULT 3,
                    created_by INTEGER NOT NULL,
                    enabled INTEGER NOT NULL DEFAULT 1,
                    created_at INTEGER NOT NULL
                );

                CREATE TABLE IF NOT EXISTS practice_attempts (
                    draft_id TEXT NOT NULL,
                    user_id INTEGER NOT NULL,
                    attempts INTEGER NOT NULL DEFAULT 0,
                    last_attempt_at INTEGER NOT NULL DEFAULT 0,
                    PRIMARY KEY(draft_id, user_id)
                );

                CREATE INDEX IF NOT EXISTS idx_answers_session_user ON answers(session_id, user_id);
                CREATE INDEX IF NOT EXISTS idx_schedules_status_time ON schedules(status, run_at);
                CREATE INDEX IF NOT EXISTS idx_practice_token ON practice_links(token);
                """
            )
            conn.commit()

    def fetchone(self, sql: str, params: Tuple[Any, ...] = ()) -> Optional[sqlite3.Row]:
        with closing(self.connect()) as conn:
            return conn.execute(sql, params).fetchone()

    def fetchall(self, sql: str, params: Tuple[Any, ...] = ()) -> List[sqlite3.Row]:
        with closing(self.connect()) as conn:
            return conn.execute(sql, params).fetchall()

    def execute(self, sql: str, params: Tuple[Any, ...] = ()) -> None:
        with closing(self.connect()) as conn:
            conn.execute(sql, params)
            conn.commit()

    def executescript(self, script: str) -> None:
        with closing(self.connect()) as conn:
            conn.executescript(script)
            conn.commit()


DBH = DB(DB_PATH)

# ============================================================
# DB helper operations
# ============================================================


def audit(actor_id: int, action: str, target: str = "", details: Optional[Dict[str, Any]] = None) -> None:
    DBH.execute(
        "INSERT INTO audit_logs(actor_id, action, target, details, created_at) VALUES(?,?,?,?,?)",
        (actor_id, action, target, jdump(details or {}), now_ts()),
    )



def record_user(user) -> None:
    if not user:
        return
    DBH.execute(
        """
        INSERT INTO known_users(user_id, username, first_name, last_name, started, last_seen)
        VALUES(?,?,?,?,COALESCE((SELECT started FROM known_users WHERE user_id=?),0),?)
        ON CONFLICT(user_id) DO UPDATE SET
            username=excluded.username,
            first_name=excluded.first_name,
            last_name=excluded.last_name,
            last_seen=excluded.last_seen
        """,
        (user.id, user.username, user.first_name, user.last_name, user.id, now_ts()),
    )



def mark_started(user) -> None:
    record_user(user)
    DBH.execute("UPDATE known_users SET started=1, last_seen=? WHERE user_id=?", (now_ts(), user.id))



def record_chat(chat) -> None:
    if not chat:
        return
    title = getattr(chat, "title", None) or getattr(chat, "full_name", None) or getattr(chat, "username", None) or str(chat.id)
    username = getattr(chat, "username", None)
    DBH.execute(
        """
        INSERT INTO known_chats(chat_id, title, username, chat_type, active, last_seen)
        VALUES(?,?,?,?,1,?)
        ON CONFLICT(chat_id) DO UPDATE SET
            title=excluded.title,
            username=excluded.username,
            chat_type=excluded.chat_type,
            active=1,
            last_seen=excluded.last_seen
        """,
        (chat.id, title, username, chat.type, now_ts()),
    )



def is_owner(user_id: int) -> bool:
    return user_id in OWNER_SET



def is_bot_admin(user_id: int) -> bool:
    if is_owner(user_id):
        return True
    row = DBH.fetchone("SELECT 1 FROM bot_admins WHERE user_id=?", (user_id,))
    return bool(row)



def all_admin_ids() -> List[int]:
    rows = DBH.fetchall("SELECT user_id FROM bot_admins ORDER BY user_id")
    ids = [r[0] for r in rows]
    for owner_id in CONFIG.owner_ids:
        if owner_id not in ids:
            ids.insert(0, owner_id)
    dedup: List[int] = []
    seen = set()
    for uid in ids:
        if uid not in seen:
            dedup.append(uid)
            seen.add(uid)
    return dedup



def set_user_state(user_id: int, state: str, payload: Optional[Dict[str, Any]] = None) -> None:
    DBH.execute(
        "INSERT INTO user_state(user_id, state, payload, updated_at) VALUES(?,?,?,?) ON CONFLICT(user_id) DO UPDATE SET state=excluded.state, payload=excluded.payload, updated_at=excluded.updated_at",
        (user_id, state, jdump(payload or {}), now_ts()),
    )



def get_user_state(user_id: int) -> Tuple[Optional[str], Dict[str, Any]]:
    row = DBH.fetchone("SELECT state, payload FROM user_state WHERE user_id=?", (user_id,))
    if not row:
        return None, {}
    return row["state"], jload(row["payload"], {}) or {}



def clear_user_state(user_id: int) -> None:
    DBH.execute("DELETE FROM user_state WHERE user_id=?", (user_id,))



def get_active_draft_id(user_id: int) -> Optional[str]:
    row = DBH.fetchone("SELECT draft_id FROM active_drafts WHERE user_id=?", (user_id,))
    return row["draft_id"] if row else None



def set_active_draft(user_id: int, draft_id: str) -> None:
    DBH.execute(
        "INSERT INTO active_drafts(user_id, draft_id, updated_at) VALUES(?,?,?) ON CONFLICT(user_id) DO UPDATE SET draft_id=excluded.draft_id, updated_at=excluded.updated_at",
        (user_id, draft_id, now_ts()),
    )



def clear_active_draft(user_id: int) -> None:
    DBH.execute("DELETE FROM active_drafts WHERE user_id=?", (user_id,))



def ensure_practice_link(draft_id: str, created_by: int, max_attempts: int = 3) -> sqlite3.Row:
    row = DBH.fetchone("SELECT * FROM practice_links WHERE draft_id=?", (draft_id,))
    if row:
        if int(row["max_attempts"]) != max_attempts:
            DBH.execute("UPDATE practice_links SET max_attempts=?, enabled=1 WHERE draft_id=?", (max_attempts, draft_id))
            row = DBH.fetchone("SELECT * FROM practice_links WHERE draft_id=?", (draft_id,))
        return row
    token = short_uuid() + short_uuid()
    DBH.execute(
        "INSERT INTO practice_links(draft_id, token, max_attempts, created_by, enabled, created_at) VALUES(?,?,?,?,1,?)",
        (draft_id, token, max_attempts, created_by, now_ts()),
    )
    return DBH.fetchone("SELECT * FROM practice_links WHERE draft_id=?", (draft_id,))


def get_practice_link_by_token(token: str) -> Optional[sqlite3.Row]:
    return DBH.fetchone(
        "SELECT pl.*, d.title, d.question_time, d.negative_mark FROM practice_links pl JOIN drafts d ON d.id=pl.draft_id WHERE pl.token=? AND pl.enabled=1",
        (token,),
    )


def get_practice_attempts(draft_id: str, user_id: int) -> int:
    row = DBH.fetchone("SELECT attempts FROM practice_attempts WHERE draft_id=? AND user_id=?", (draft_id, user_id))
    return int(row["attempts"] if row else 0)


def register_practice_attempt(draft_id: str, user_id: int) -> int:
    attempts = get_practice_attempts(draft_id, user_id) + 1
    DBH.execute(
        "INSERT INTO practice_attempts(draft_id, user_id, attempts, last_attempt_at) VALUES(?,?,?,?) "
        "ON CONFLICT(draft_id, user_id) DO UPDATE SET attempts=excluded.attempts, last_attempt_at=excluded.last_attempt_at",
        (draft_id, user_id, attempts, now_ts()),
    )
    return attempts


def get_draft(draft_id: str) -> Optional[sqlite3.Row]:
    return DBH.fetchone("SELECT * FROM drafts WHERE id=?", (draft_id,))



def get_draft_questions(draft_id: str) -> List[sqlite3.Row]:
    return DBH.fetchall("SELECT * FROM draft_questions WHERE draft_id=? ORDER BY q_no", (draft_id,))



def get_bound_draft(chat_id: int) -> Optional[sqlite3.Row]:
    return DBH.fetchone(
        """
        SELECT d.*, b.updated_at AS bound_at, b.created_by
        FROM group_bindings b
        JOIN drafts d ON d.id = b.draft_id
        WHERE b.chat_id=?
        """,
        (chat_id,),
    )



def get_active_session(chat_id: int) -> Optional[sqlite3.Row]:
    return DBH.fetchone(
        "SELECT * FROM sessions WHERE chat_id=? AND status IN ('countdown','running') ORDER BY started_at DESC LIMIT 1",
        (chat_id,),
    )



def get_session(session_id: str) -> Optional[sqlite3.Row]:
    return DBH.fetchone("SELECT * FROM sessions WHERE id=?", (session_id,))



def get_session_question(session_id: str, q_no: int) -> Optional[sqlite3.Row]:
    return DBH.fetchone("SELECT * FROM session_questions WHERE session_id=? AND q_no=?", (session_id, q_no))



def get_question_by_poll(poll_id: str) -> Optional[sqlite3.Row]:
    return DBH.fetchone(
        """
        SELECT sq.*, s.chat_id, s.title, s.question_time, s.negative_mark, s.total_questions, s.status AS session_status
        FROM session_questions sq
        JOIN sessions s ON s.id = sq.session_id
        WHERE sq.poll_id=?
        """,
        (poll_id,),
    )



def list_user_drafts(user_id: int) -> List[sqlite3.Row]:
    return DBH.fetchall(
        "SELECT d.*, COUNT(q.id) AS q_count FROM drafts d LEFT JOIN draft_questions q ON q.draft_id=d.id WHERE d.owner_id=? GROUP BY d.id ORDER BY d.updated_at DESC",
        (user_id,),
    )



def list_ready_drafts() -> List[sqlite3.Row]:
    return DBH.fetchall(
        "SELECT d.*, COUNT(q.id) AS q_count FROM drafts d LEFT JOIN draft_questions q ON q.draft_id=d.id GROUP BY d.id HAVING q_count > 0 ORDER BY d.updated_at DESC"
    )



def list_group_schedules(chat_id: int) -> List[sqlite3.Row]:
    return DBH.fetchall(
        """
        SELECT s.*, d.title
        FROM schedules s
        JOIN drafts d ON d.id=s.draft_id
        WHERE s.chat_id=? AND s.status='scheduled'
        ORDER BY s.run_at ASC
        """,
        (chat_id,),
    )



def build_commands_text(chat_type: str, is_admin_user: bool, is_owner_user: bool) -> str:
    lines: List[str] = ["<b>Command List</b>", "সব command <b>/</b> এবং <b>.</b> — দুই prefix এই কাজ করবে।", ""]
    if chat_type == "private":
        lines.extend([
            "<b>Everyone</b>",
            "• /start — bot activate / result DM enable",
            "• /start practice_TOKEN — practice exam start (via generated link)",
            "• /help or /commands — command list",
        ])
        if is_admin_user:
            lines.extend([
                "",
                "<b>Admin / Owner (PM)</b>",
                "• /panel — admin button panel",
                "• /newexam — new exam draft create",
                "• /drafts or /mydrafts — my drafts list",
                "• /csvformat — CSV column format",
                "• /cancel — current input flow cancel",
            ])
        if is_owner_user:
            lines.extend([
                "",
                "<b>Owner Only (PM)</b>",
                "• /addadmin [user_id] — add bot admin",
                "• /rmadmin [user_id] — remove bot admin",
                "• /admins — admin list",
                "• /audit — recent admin actions",
                "• /logs — memory, uptime, recent errors + full log",
                "• /broadcast [pin] — send to all groups + started users",
                "• /announce CHAT_ID [pin] — send to one chat",
                "• /restart — restart bot process",
            ])
    else:
        lines.extend([
            "<b>Group Admin / Bot Admin</b>",
            "• /binddraft CODE — bind draft manually (optional if active draft exists)",
            "• /examstatus — current binding/exam status",
            "• /starttqex [DRAFTCODE] — show ready button / start selected exam",
            "• /stoptqex — stop running exam",
            "• /schedule YYYY-MM-DD HH:MM — schedule exam",
            "• /listschedules — list scheduled exams",
            "• /cancelschedule SCHEDULE_ID — cancel schedule",
        ])
    return "\n".join(lines)


async def send_commands_text(message: Message, context: ContextTypes.DEFAULT_TYPE) -> None:
    user = message.from_user
    if not user:
        return
    text = build_commands_text(
        message.chat.type,
        is_admin_user=is_bot_admin(user.id),
        is_owner_user=is_owner(user.id),
    )
    await safe_reply(message, text, parse_mode=ParseMode.HTML)


async def send_csv_format_help(message: Message) -> None:
    text = (
        "<b>CSV Format</b>\n"
        "Required columns: <code>questions, option1, option2, answer</code>\n"
        "Optional columns: <code>option3 ... option10, explanation, type, section</code>\n\n"
        "<b>answer</b> field এ option number (1,2,3...) অথবা exact option text দিতে পারবেন।\n\n"
        "<b>Example header</b>\n"
        "<code>questions,option1,option2,option3,option4,answer,explanation</code>"
    )
    await safe_reply(message, text, parse_mode=ParseMode.HTML)


# ============================================================
# Font and rendering helpers
# ============================================================

FONT_CANDIDATES = {
    "regular": [
        str(FONTS_DIR / "NotoSansBengali-Regular.ttf"),
        str(FONTS_DIR / "NotoSans-Regular.ttf"),
        str(FONTS_DIR / "NotoSansBengali-Bold.ttf"),
        "/usr/share/fonts/truetype/noto/NotoSansBengali-Regular.ttf",
        "/usr/share/fonts/truetype/noto/NotoSerifBengali-Regular.ttf",
        "/usr/share/fonts/truetype/lohit-bengali/Lohit-Bengali.ttf",
        "/usr/share/fonts/truetype/noto/NotoSans-Regular.ttf",
        "/usr/share/fonts/truetype/freefont/FreeSans.ttf",
        "/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf",
    ],
    "bold": [
        str(FONTS_DIR / "NotoSansBengali-Bold.ttf"),
        str(FONTS_DIR / "NotoSans-Bold.ttf"),
        str(FONTS_DIR / "NotoSansBengali-Regular.ttf"),
        "/usr/share/fonts/truetype/noto/NotoSansBengali-Bold.ttf",
        "/usr/share/fonts/truetype/noto/NotoSerifBengali-Bold.ttf",
        "/usr/share/fonts/truetype/noto/NotoSans-Bold.ttf",
        "/usr/share/fonts/truetype/freefont/FreeSansBold.ttf",
        "/usr/share/fonts/truetype/dejavu/DejaVuSans-Bold.ttf",
    ],
    "emoji": [
        str(FONTS_DIR / "NotoColorEmoji.ttf"),
        "/usr/share/fonts/truetype/noto/NotoColorEmoji.ttf",
        "/usr/share/fonts/truetype/noto/NotoEmoji-Regular.ttf",
        "/usr/share/fonts/truetype/noto/NotoSansSymbols2-Regular.ttf",
        "/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf",
    ],
}


def _expand_font_candidates(kind: str) -> List[str]:
    patterns = list(FONT_CANDIDATES.get(kind, []))
    if kind in {"regular", "bold"}:
        patterns.extend([
            str(FONTS_DIR / "Noto*Bengali*.ttf"),
            str(FONTS_DIR / "NotoSans*.ttf"),
            str(FONTS_DIR / "*.ttf"),
            "/usr/share/fonts/truetype/noto/Noto*Bengali*.ttf",
            "/usr/share/fonts/truetype/lohit-bengali/*.ttf",
            "/usr/share/fonts/truetype/noto/NotoSans*.ttf",
            "/usr/share/fonts/truetype/freefont/*.ttf",
            "/usr/share/fonts/truetype/dejavu/*.ttf",
        ])
    seen: List[str] = []
    for pattern in patterns:
        matches = glob(pattern) if any(ch in pattern for ch in '*?[') else [pattern]
        for path in matches:
            if path not in seen and os.path.exists(path):
                seen.append(path)
    return seen


def find_font(kind: str, size: int) -> ImageFont.FreeTypeFont | ImageFont.ImageFont:
    layout_engine = None
    with suppress(Exception):
        layout_engine = getattr(ImageFont, "Layout").RAQM
    for path in _expand_font_candidates(kind):
        with suppress(Exception):
            if layout_engine is not None:
                return ImageFont.truetype(path, size=size, layout_engine=layout_engine)
            return ImageFont.truetype(path, size=size)
    return ImageFont.load_default()


class FontPack:
    def __init__(self):
        self.cache: Dict[Tuple[str, int], Any] = {}

    def get(self, kind: str, size: int):
        key = (kind, size)
        if key not in self.cache:
            self.cache[key] = find_font(kind, size)
        return self.cache[key]


FONTS = FontPack()


def wrap_text(draw: ImageDraw.ImageDraw, text: str, font, max_width: int) -> List[str]:
    text = (text or "").replace("\r", "")
    if not text:
        return [""]
    raw_lines = text.split("\n")
    out_lines: List[str] = []
    for raw in raw_lines:
        line = raw.strip()
        if not line:
            out_lines.append("")
            continue
        words = line.split()
        current = words[0]
        for word in words[1:]:
            trial = f"{current} {word}"
            bbox = draw.textbbox((0, 0), trial, font=font)
            if bbox[2] - bbox[0] <= max_width:
                current = trial
                continue
            out_lines.append(current)
            current = word
        out_lines.append(current)
    return out_lines or [""]


def draw_multiline(draw: ImageDraw.ImageDraw, text: str, xy: Tuple[int, int], font, fill, max_width: int, line_gap: int = 10) -> Tuple[int, int]:
    x, y = xy
    lines = wrap_text(draw, text, font, max_width)
    max_x = x
    for line in lines:
        draw.text((x, y), line, font=font, fill=fill)
        bbox = draw.textbbox((x, y), line or " ", font=font)
        y += (bbox[3] - bbox[1]) + line_gap
        max_x = max(max_x, bbox[2])
    return max_x, y


def render_leaderboard_png(title: str, items: List[Dict[str, Any]]) -> bytes:
    width = 1600
    title = (title or "").strip() or "Exam"
    working = items or [{"name": "No eligible participants", "sub": "", "score": "0.00"}]
    header_lines_est = max(1, len(wrap_text(ImageDraw.Draw(Image.new("RGB", (10, 10))), f"LEADERBOARD — {title}", FONTS.get("bold", 68), width - 120)))
    height = 280 + header_lines_est * 82 + max(1, len(working)) * 118 + 110
    img = Image.new("RGB", (width, height), "#03101F")
    draw = ImageDraw.Draw(img)

    title_font = FONTS.get("bold", 68)
    sub_font = FONTS.get("regular", 33)
    head_font = FONTS.get("bold", 42)
    row_font = FONTS.get("regular", 39)
    sub_row_font = FONTS.get("regular", 24)
    score_font = FONTS.get("bold", 48)
    small_font = FONTS.get("regular", 24)

    _, title_bottom = draw_multiline(draw, f"LEADERBOARD — {title}", (60, 36), title_font, "#EAF2FF", width - 120, line_gap=8)
    draw.text((60, title_bottom + 2), "Top performers (score includes negative marking)", font=sub_font, fill="#B9C7DD")

    table_x = 50
    table_y = title_bottom + 70
    table_w = width - 100
    draw.rounded_rectangle((table_x, table_y, table_x + table_w, table_y + 88), radius=24, fill="#07162D")
    draw.text((table_x + 32, table_y + 22), "Rank", font=head_font, fill="#F5F7FF")
    draw.text((table_x + 190, table_y + 22), "Name", font=head_font, fill="#F5F7FF")
    draw.text((table_x + table_w - 220, table_y + 22), "Score", font=head_font, fill="#F5F7FF")

    y = table_y + 112
    for idx, item in enumerate(working, start=1):
        fill = "#132744" if idx == 1 else "#0E2037"
        draw.rounded_rectangle((table_x, y, table_x + table_w, y + 96), radius=24, fill=fill)
        draw.text((table_x + 34, y + 21), str(idx), font=head_font, fill="#F8FBFF")
        name = (item.get("name") or "Unknown").strip()
        sub = (item.get("sub") or "").strip()
        score = item.get("score") or "0.00"
        max_name_w = table_w - 540
        name_lines = wrap_text(draw, name, row_font, max_name_w)
        draw.text((table_x + 185, y + 15), name_lines[0], font=row_font, fill="#EDF4FF")
        if sub:
            sub_show = sub if len(sub) <= 28 else sub[:27] + "…"
            draw.text((table_x + 188, y + 56), sub_show, font=sub_row_font, fill="#C8D8F4")
        elif len(name_lines) > 1:
            draw.text((table_x + 188, y + 56), name_lines[1], font=sub_row_font, fill="#C8D8F4")
        sb = draw.textbbox((0, 0), str(score), font=score_font)
        draw.text((table_x + table_w - 70 - (sb[2] - sb[0]), y + 19), str(score), font=score_font, fill="#D7F7CC")
        y += 116

    draw.text((60, height - 52), f"Generated by {CONFIG.brand_name}", font=small_font, fill="#95A0B4")
    buf = io.BytesIO()
    img.save(buf, format="PNG", optimize=True)
    return buf.getvalue()


def render_report_pdf(title: str, summary: Dict[str, Any], ranking: List[Dict[str, Any]], qstats: List[Dict[str, Any]]) -> bytes:
    pages: List[Image.Image] = []
    width, height = 1654, 2339  # A4-ish at 150 dpi
    title_font = FONTS.get("bold", 52)
    section_font = FONTS.get("bold", 30)
    body_font = FONTS.get("regular", 24)
    small_font = FONTS.get("regular", 20)

    def new_page() -> Tuple[Image.Image, ImageDraw.ImageDraw, int]:
        page = Image.new("RGB", (width, height), "#FFFFFF")
        dr = ImageDraw.Draw(page)
        dr.rounded_rectangle((40, 40, width - 40, height - 40), radius=26, outline="#D8E2EF", width=3)
        dr.text((72, 70), f"{CONFIG.brand_name} • Exam Report", font=section_font, fill="#18324B")
        _, bottom = draw_multiline(dr, title or "Exam", (72, 118), title_font, "#101820", width - 144, line_gap=6)
        dr.text((72, bottom + 4), f"Generated at {fmt_dt(now_ts())}", font=small_font, fill="#6B7A8B")
        return page, dr, bottom + 46

    def draw_key_values(dr, y, items):
        left = 72
        box_w = (width - 144 - 18) // 2
        row_h = 76
        for idx, (k, v) in enumerate(items):
            col = idx % 2
            row = idx // 2
            x1 = left + col * (box_w + 18)
            y1 = y + row * (row_h + 16)
            dr.rounded_rectangle((x1, y1, x1 + box_w, y1 + row_h), radius=18, fill="#F6FAFD", outline="#DCE8F2")
            dr.text((x1 + 24, y1 + 14), str(k), font=small_font, fill="#587086")
            dr.text((x1 + 24, y1 + 38), str(v), font=section_font, fill="#0F2235")
        rows = (len(items) + 1) // 2
        return y + rows * (row_h + 16)

    page, dr, y = new_page()
    y = draw_key_values(dr, y, [
        ("Participants", summary["participants"]),
        ("Questions", summary["questions"]),
        ("Average Score", summary["average_score"]),
        ("Highest Score", summary["highest_score"]),
        ("Lowest Score", summary["lowest_score"]),
        ("Negative / Wrong", summary["negative_mark"]),
        ("Started", summary["started_at"]),
        ("Ended", summary["ended_at"]),
    ])
    y += 16
    dr.text((72, y), "Ranking Summary", font=section_font, fill="#18324B")
    y += 44
    header = (72, y, width - 72, y + 48)
    dr.rounded_rectangle(header, radius=14, fill="#0F2235")
    cols = [(92, "#"), (150, "Name"), (920, "Correct"), (1080, "Wrong"), (1230, "Skipped"), (1400, "Score")]
    for x, label in cols:
        dr.text((x, y + 12), label, font=small_font, fill="#FFFFFF")
    y += 62
    row_h = 50
    for item in ranking[:24]:
        dr.rounded_rectangle((72, y, width - 72, y + row_h), radius=12, fill="#F8FBFE", outline="#DFE8F1")
        name = item["name"]
        if item.get("sub_name"):
            name = f"{name} ({item['sub_name']})"
        name = name[:44] + ("…" if len(name) > 44 else "")
        dr.text((92, y + 12), str(item["rank"]), font=body_font, fill="#102030")
        dr.text((150, y + 12), name, font=body_font, fill="#102030")
        dr.text((940, y + 12), str(item["correct"]), font=body_font, fill="#1C7C38")
        dr.text((1100, y + 12), str(item["wrong"]), font=body_font, fill="#B94040")
        dr.text((1255, y + 12), str(item["skipped"]), font=body_font, fill="#A77412")
        dr.text((1405, y + 12), str(item["score"]), font=body_font, fill="#102030")
        y += row_h + 10
        if y > height - 280:
            pages.append(page)
            page, dr, y = new_page()
    pages.append(page)

    # Full ranking pages
    full_rows = ranking or [{"rank": 1, "name": "No eligible participants", "sub_name": "", "correct": 0, "wrong": 0, "skipped": int(summary["questions"]), "score": "0.00"}]
    rank_chunks = list(chunked(full_rows, 30))
    for chunk_index, chunk in enumerate(rank_chunks, start=1):
        page, dr, y = new_page()
        dr.text((72, y), f"Detailed Ranking • Page {chunk_index}/{len(rank_chunks)}", font=section_font, fill="#18324B")
        y += 44
        dr.rounded_rectangle((72, y, width - 72, y + 48), radius=14, fill="#0F2235")
        for x, label in cols:
            dr.text((x, y + 12), label, font=small_font, fill="#FFFFFF")
        y += 60
        for item in chunk:
            dr.rounded_rectangle((72, y, width - 72, y + row_h), radius=12, fill="#F8FBFE", outline="#DFE8F1")
            primary = item["name"][:34] + ("…" if len(item["name"]) > 34 else "")
            sub = item.get("sub_name", "")
            dr.text((92, y + 12), str(item["rank"]), font=body_font, fill="#102030")
            dr.text((150, y + 8), primary, font=body_font, fill="#102030")
            if sub:
                dr.text((150, y + 28), sub[:28] + ("…" if len(sub) > 28 else ""), font=small_font, fill="#627B90")
            dr.text((940, y + 12), str(item["correct"]), font=body_font, fill="#1C7C38")
            dr.text((1100, y + 12), str(item["wrong"]), font=body_font, fill="#B94040")
            dr.text((1255, y + 12), str(item["skipped"]), font=body_font, fill="#A77412")
            dr.text((1405, y + 12), str(item["score"]), font=body_font, fill="#102030")
            y += row_h + 10
        pages.append(page)

    q_chunks = list(chunked(qstats, 30)) or [[]]
    for chunk_index, chunk in enumerate(q_chunks, start=1):
        page, dr, y = new_page()
        dr.text((72, y), f"Question Analytics • Page {chunk_index}/{len(q_chunks)}", font=section_font, fill="#18324B")
        y += 44
        dr.rounded_rectangle((72, y, width - 72, y + 48), radius=14, fill="#0F2235")
        headers = [(92, "Q"), (170, "Correct"), (320, "Wrong"), (450, "Skipped"), (600, "Question Preview")]
        for x, label in headers:
            dr.text((x, y + 12), label, font=small_font, fill="#FFFFFF")
        y += 60
        for item in chunk:
            dr.rounded_rectangle((72, y, width - 72, y + 56), radius=12, fill="#F8FBFE", outline="#DFE8F1")
            preview = str(item["preview"]).replace("\n", " ").strip()
            preview = preview[:62] + ("…" if len(preview) > 62 else "")
            dr.text((92, y + 15), str(item["q_no"]), font=body_font, fill="#102030")
            dr.text((175, y + 15), str(item["correct"]), font=body_font, fill="#1C7C38")
            dr.text((325, y + 15), str(item["wrong"]), font=body_font, fill="#B94040")
            dr.text((455, y + 15), str(item["skipped"]), font=body_font, fill="#A77412")
            dr.text((600, y + 15), preview, font=body_font, fill="#102030")
            y += 66
        pages.append(page)

    rgb_pages = [p.convert("RGB") for p in pages]
    buf = io.BytesIO()
    rgb_pages[0].save(buf, format="PDF", save_all=True, append_images=rgb_pages[1:], resolution=150.0)
    return buf.getvalue()


async def ensure_fonts_hint_file() -> str:
    return (
        "fonts/ এর মধ্যে ideally এই 4টা file রাখুন: NotoSansBengali-Regular.ttf, "
        "NotoSansBengali-Bold.ttf, NotoSans-Regular.ttf, NotoSans-Bold.ttf"
    )

# ============================================================
# Access and exam logic
# ============================================================

async def is_required_channel_member(context: ContextTypes.DEFAULT_TYPE, user_id: int) -> bool:
    channel = CONFIG.required_channel
    if not channel:
        return True
    try:
        member = await context.bot.get_chat_member(channel, user_id)
        blocked_statuses = {getattr(ChatMemberStatus, 'LEFT', 'left'), getattr(ChatMemberStatus, 'BANNED', 'kicked'), getattr(ChatMemberStatus, 'KICKED', 'kicked')}
        return member.status not in blocked_statuses
    except TelegramError:
        return False


async def is_group_admin_or_global(update: Update, context: ContextTypes.DEFAULT_TYPE) -> bool:
    user = update.effective_user
    chat = update.effective_chat
    if not user or not chat:
        return False
    if is_bot_admin(user.id):
        return True
    try:
        member = await context.bot.get_chat_member(chat.id, user.id)
        return member.status in {ChatMemberStatus.ADMINISTRATOR, ChatMemberStatus.OWNER}
    except TelegramError:
        return False


async def safe_reply(message: Message, text: str, **kwargs):
    with suppress(TelegramError):
        return await message.reply_text(text, **kwargs)
    return None


async def safe_delete_message(bot, chat_id: int, message_id: int) -> None:
    with suppress(TelegramError):
        await bot.delete_message(chat_id=chat_id, message_id=message_id)


async def safe_pin_message(bot, chat_id: int, message_id: int) -> None:
    with suppress(TelegramError):
        await bot.pin_chat_message(chat_id=chat_id, message_id=message_id, disable_notification=True)


async def schedule_delete(bot, chat_id: int, message_id: int, seconds: int) -> None:
    await asyncio.sleep(max(0, seconds))
    await safe_delete_message(bot, chat_id, message_id)


async def delete_service_pin_later(context: ContextTypes.DEFAULT_TYPE, chat_id: int) -> None:
    context.bot_data.setdefault("pin_cleanup_until", {})[chat_id] = now_ts() + 15


async def send_temporary_group_warning(context: ContextTypes.DEFAULT_TYPE, chat_id: int, text: str) -> None:
    try:
        msg = await context.bot.send_message(chat_id, text)
    except TelegramError:
        return
    context.job_queue.run_once(
        lambda c: c.application.create_task(safe_delete_message(c.bot, chat_id, msg.message_id)),
        when=max(150, CONFIG.delete_delay_seconds),
        name=f"warn_del:{chat_id}:{msg.message_id}",
    )


async def handle_group_denied_command(update: Update, context: ContextTypes.DEFAULT_TYPE, text: Optional[str] = None) -> None:
    message = update.effective_message
    chat = update.effective_chat
    if not message or not chat:
        return
    await safe_delete_message(context.bot, chat.id, message.message_id)
    await send_temporary_group_warning(context, chat.id, text or warning_text())



async def start_practice_from_token(update: Update, context: ContextTypes.DEFAULT_TYPE, token: str) -> None:
    message = update.effective_message
    user = update.effective_user
    if not message or not user:
        return
    record_user(user)
    mark_started(user)
    joined = await is_required_channel_member(context, user.id)
    if not joined:
        kb = InlineKeyboardMarkup([[InlineKeyboardButton("Join Required Channel", url=f"https://t.me/{CONFIG.required_channel.lstrip('@')}")]])
        await safe_reply(message, f"এই bot ব্যবহার করতে আগে {CONFIG.required_channel} channel এ join করুন। তারপর আবার practice link open করুন।", reply_markup=kb)
        return
    row = get_practice_link_by_token(token)
    if not row:
        await safe_reply(message, "এই practice link invalid বা disabled।")
        return
    q_count_row = DBH.fetchone("SELECT COUNT(*) AS c FROM draft_questions WHERE draft_id=?", (row["draft_id"],))
    q_count = int(q_count_row["c"] if q_count_row else 0)
    if q_count <= 0:
        await safe_reply(message, "এই practice exam এ এখনও কোনো প্রশ্ন নেই।")
        return
    attempts = get_practice_attempts(row["draft_id"], user.id)
    max_attempts = int(row["max_attempts"])
    if attempts >= max_attempts:
        await safe_reply(message, f"আপনি এই practice exam সর্বোচ্চ {max_attempts} বার দিয়েছেন।")
        return
    if get_active_session(user.id):
        await safe_reply(message, "আপনার inbox এ ইতিমধ্যে একটি চলমান exam/practice আছে। শেষ হলে আবার চেষ্টা করুন।")
        return
    new_attempt = register_practice_attempt(row["draft_id"], user.id)
    session_id = create_session_from_draft(row["draft_id"], user.id, user.id)
    if not session_id:
        await safe_reply(message, "Practice session create করা যায়নি।")
        return
    await safe_reply(
        message,
        f"<b>Practice Ready</b>\n"
        f"<b>{html_escape(row['title'])}</b>\n"
        f"Questions: <b>{q_count}</b>\n"
        f"Time / question: <b>{row['question_time']} sec</b>\n"
        f"Negative / wrong: <b>{row['negative_mark']}</b>\n"
        f"Attempt: <b>{new_attempt}/{max_attempts}</b>",
        parse_mode=ParseMode.HTML,
    )
    await start_exam_countdown(context, session_id)


def create_draft(owner_id: int, title: str, question_time: int, negative_mark: float) -> str:
    draft_id = short_uuid()
    ts = now_ts()
    DBH.execute(
        "INSERT INTO drafts(id, owner_id, title, question_time, negative_mark, status, created_at, updated_at) VALUES(?,?,?,?,?,?,?,?)",
        (draft_id, owner_id, title, question_time, negative_mark, "draft", ts, ts),
    )
    set_active_draft(owner_id, draft_id)
    audit(owner_id, "create_draft", draft_id, {"title": title, "question_time": question_time, "negative_mark": negative_mark})
    return draft_id



def refresh_draft_status(draft_id: str) -> None:
    row = DBH.fetchone("SELECT COUNT(*) AS c FROM draft_questions WHERE draft_id=?", (draft_id,))
    c = int(row["c"] if row else 0)
    status = "ready" if c > 0 else "draft"
    DBH.execute("UPDATE drafts SET status=?, updated_at=? WHERE id=?", (status, now_ts(), draft_id))



def add_question_to_draft(draft_id: str, question: str, options: List[str], correct_option: int, explanation: str, src: str) -> int:
    row = DBH.fetchone("SELECT COALESCE(MAX(q_no), 0) AS mx FROM draft_questions WHERE draft_id=?", (draft_id,))
    q_no = int(row["mx"] or 0) + 1
    DBH.execute(
        "INSERT INTO draft_questions(draft_id, q_no, question, options, correct_option, explanation, src) VALUES(?,?,?,?,?,?,?)",
        (draft_id, q_no, question.strip(), jdump(options), int(correct_option), explanation.strip(), src),
    )
    refresh_draft_status(draft_id)
    return q_no



def delete_draft(draft_id: str, actor_id: int) -> None:
    draft = get_draft(draft_id)
    if draft:
        DBH.execute("DELETE FROM drafts WHERE id=?", (draft_id,))
        DBH.execute("DELETE FROM active_drafts WHERE draft_id=?", (draft_id,))
        DBH.execute("DELETE FROM group_bindings WHERE draft_id=?", (draft_id,))
        audit(actor_id, "delete_draft", draft_id, {"title": draft['title']})



def import_csv_questions(file_bytes: bytes, draft_id: str) -> Tuple[int, List[str]]:
    added = 0
    errors: List[str] = []
    text = file_bytes.decode("utf-8-sig", errors="replace")
    reader = csv.DictReader(io.StringIO(text))
    for idx, row in enumerate(reader, start=2):
        normalized = {str(k or "").strip().lower(): (v or "").strip() for k, v in row.items()}
        question = normalized.get("questions") or normalized.get("question") or normalized.get("q")
        if not question:
            errors.append(f"Row {idx}: missing question")
            continue
        options: List[str] = []
        for i in range(1, 11):
            value = normalized.get(f"option{i}")
            if value:
                options.append(value)
        if len(options) < 2:
            errors.append(f"Row {idx}: need at least 2 options")
            continue
        ans_raw = normalized.get("answer", "")
        correct_idx: Optional[int] = None
        if ans_raw.isdigit():
            n = int(ans_raw)
            if 1 <= n <= len(options):
                correct_idx = n - 1
        if correct_idx is None:
            for i, opt in enumerate(options):
                if opt.strip() == ans_raw.strip() and ans_raw:
                    correct_idx = i
                    break
        if correct_idx is None:
            errors.append(f"Row {idx}: invalid answer")
            continue
        explanation = normalized.get("explanation", "")
        add_question_to_draft(draft_id, question, options, correct_idx, explanation, f"csv:{idx}")
        added += 1
    return added, errors



def bind_draft_to_group(draft_id: str, chat_id: int, actor_id: int) -> None:
    DBH.execute(
        "INSERT INTO group_bindings(chat_id, draft_id, created_by, updated_at) VALUES(?,?,?,?) ON CONFLICT(chat_id) DO UPDATE SET draft_id=excluded.draft_id, created_by=excluded.created_by, updated_at=excluded.updated_at",
        (chat_id, draft_id, actor_id, now_ts()),
    )
    audit(actor_id, "bind_draft", str(chat_id), {"draft_id": draft_id})



def create_session_from_draft(draft_id: str, chat_id: int, actor_id: int) -> Optional[str]:
    draft = get_draft(draft_id)
    if not draft:
        return None
    questions = get_draft_questions(draft_id)
    if not questions:
        return None
    session_id = short_uuid() + short_uuid()
    started = now_ts()
    DBH.execute(
        "INSERT INTO sessions(id, chat_id, draft_id, title, question_time, negative_mark, total_questions, current_index, status, started_at, created_by) VALUES(?,?,?,?,?,?,?,?,?,?,?)",
        (
            session_id,
            chat_id,
            draft_id,
            draft["title"],
            draft["question_time"],
            draft["negative_mark"],
            len(questions),
            0,
            "countdown",
            started,
            actor_id,
        ),
    )
    with closing(DBH.connect()) as conn:
        for q in questions:
            conn.execute(
                "INSERT INTO session_questions(session_id, q_no, question, options, correct_option, explanation) VALUES(?,?,?,?,?,?)",
                (session_id, q["q_no"], q["question"], q["options"], q["correct_option"], q["explanation"]),
            )
        conn.commit()
    audit(actor_id, "create_session", session_id, {"chat_id": chat_id, "draft_id": draft_id})
    return session_id



def create_session_from_bound_draft(chat_id: int, actor_id: int) -> Optional[str]:
    draft = get_bound_draft(chat_id)
    if not draft:
        return None
    return create_session_from_draft(draft["id"], chat_id, actor_id)


def resolve_group_draft_for_actor(chat_id: int, actor_id: int) -> Optional[sqlite3.Row]:
    bound = get_bound_draft(chat_id)
    if bound:
        return bound
    active_id = get_active_draft_id(actor_id)
    if not active_id:
        return None
    draft = get_draft(active_id)
    if not draft:
        return None
    q_count = DBH.fetchone("SELECT COUNT(*) AS c FROM draft_questions WHERE draft_id=?", (active_id,))
    if int(q_count['c'] if q_count else 0) <= 0:
        return None
    bind_draft_to_group(active_id, chat_id, actor_id)
    return get_draft(active_id)



def get_session_ranking(session_id: str) -> List[Dict[str, Any]]:
    session = get_session(session_id)
    if not session:
        return []
    rows = DBH.fetchall(
        """
        SELECT p.*, ku.first_name, ku.last_name
        FROM participants p
        LEFT JOIN known_users ku ON ku.user_id = p.user_id
        WHERE p.session_id=? AND p.eligible=1
        ORDER BY p.score DESC, p.correct_count DESC, p.wrong_count ASC, p.last_answer_at ASC, p.user_id ASC
        """,
        (session_id,),
    )
    ranking: List[Dict[str, Any]] = []
    total_questions = int(session["total_questions"])
    for rank, row in enumerate(rows, start=1):
        answered = DBH.fetchone("SELECT COUNT(*) AS c FROM answers WHERE session_id=? AND user_id=?", (session_id, row["user_id"]))
        answered_count = int(answered["c"] if answered else 0)
        full = " ".join(x for x in [row["first_name"], row["last_name"]] if x).strip()
        main_name, sub_name = split_user_labels(full or row["display_name"], row["username"], int(row["user_id"]))
        ranking.append(
            {
                "rank": rank,
                "user_id": row["user_id"],
                "name": main_name,
                "sub_name": sub_name,
                "correct": int(row["correct_count"]),
                "wrong": int(row["wrong_count"]),
                "skipped": max(0, total_questions - answered_count),
                "score": fmt_score(float(row["score"])),
            }
        )
    return ranking



def get_question_analytics(session_id: str) -> List[Dict[str, Any]]:
    session = get_session(session_id)
    if not session:
        return []
    participants = DBH.fetchone("SELECT COUNT(*) AS c FROM participants WHERE session_id=? AND eligible=1", (session_id,))
    total_participants = int(participants["c"] if participants else 0)
    rows = DBH.fetchall("SELECT * FROM session_questions WHERE session_id=? ORDER BY q_no", (session_id,))
    items: List[Dict[str, Any]] = []
    for row in rows:
        counts = DBH.fetchall(
            "SELECT is_correct, COUNT(*) AS c FROM answers WHERE session_id=? AND q_no=? GROUP BY is_correct",
            (session_id, row["q_no"]),
        )
        correct = 0
        wrong = 0
        for c in counts:
            if int(c["is_correct"]) == 1:
                correct = int(c["c"])
            else:
                wrong = int(c["c"])
        answered = correct + wrong
        items.append(
            {
                "q_no": int(row["q_no"]),
                "correct": correct,
                "wrong": wrong,
                "skipped": max(0, total_participants - answered),
                "preview": row["question"],
            }
        )
    return items



def set_session_active_poll(session_id: str, poll_id: Optional[str], message_id: Optional[int]) -> None:
    DBH.execute(
        "UPDATE sessions SET active_poll_id=?, active_poll_message_id=? WHERE id=?",
        (poll_id, message_id, session_id),
    )



def mark_session_countdown_message(session_id: str, message_id: int) -> None:
    DBH.execute("UPDATE sessions SET countdown_message_id=? WHERE id=?", (message_id, session_id))



def mark_session_status_message(session_id: str, message_id: int) -> None:
    DBH.execute("UPDATE sessions SET status_message_id=? WHERE id=?", (message_id, session_id))



def queue_delete(kind: str, ref_id: str, delete_after_ts: int) -> None:
    DBH.execute(
        "INSERT OR REPLACE INTO delete_queue(kind, ref_id, delete_after) VALUES(?,?,?)",
        (kind, ref_id, delete_after_ts),
    )



def cleanup_session_data(session_id: str) -> None:
    DBH.execute("DELETE FROM sessions WHERE id=?", (session_id,))



def finalize_scores(session_id: str) -> None:
    session = get_session(session_id)
    if not session:
        return
    total_questions = int(session["total_questions"])
    participant_rows = DBH.fetchall("SELECT * FROM participants WHERE session_id=?", (session_id,))
    for p in participant_rows:
        answered = DBH.fetchone("SELECT COUNT(*) AS c FROM answers WHERE session_id=? AND user_id=?", (session_id, p["user_id"]))
        answered_count = int(answered["c"] if answered else 0)
        skipped = max(0, total_questions - answered_count)
        # skipped stored only in report, not in table
        _ = skipped


async def send_draft_card(context: ContextTypes.DEFAULT_TYPE, chat_id: int, user_id: int, draft_id: str, header: str = "") -> None:
    draft = get_draft(draft_id)
    if not draft:
        await context.bot.send_message(chat_id, "এই draft আর নেই।")
        return
    q_rows = get_draft_questions(draft_id)
    count = len(q_rows)
    practice_line = ""
    bot_username = context.bot_data.get("bot_username", "")
    if count > 0 and bot_username:
        practice = ensure_practice_link(draft_id, int(draft["owner_id"]))
        practice_url = f"https://t.me/{bot_username}?start=practice_{practice['token']}"
        practice_line = (
            f"\n\n<b>Practice Link</b>\n"
            f"<a href=\"{practice_url}\">Open practice in bot inbox</a>\n"
            f"Max attempts per user: <b>{practice['max_attempts']}</b>"
        )
    text = (
        f"{header}\n" if header else ""
    ) + (
        f"<b>Draft:</b> {html_escape(draft['title'])}\n"
        f"<b>Code:</b> <code>{draft['id']}</code>\n"
        f"<b>Time / Question:</b> {draft['question_time']} sec\n"
        f"<b>Negative / Wrong:</b> {draft['negative_mark']}\n"
        f"<b>Questions:</b> {count}\n"
        f"<b>Status:</b> {'Ready' if count else 'Draft'}\n\n"
        f"এখন এই draft এ quiz forward করুন বা CSV upload করুন।\n"
        f"Target group এ <code>.binddraft {draft['id']}</code> তারপর <code>.starttqex</code> দিন।"
        f"{practice_line}"
    )
    kb_rows = [
        [
            InlineKeyboardButton("🔄 Set Active", callback_data=f"draft:set:{draft_id}"),
            InlineKeyboardButton("🗑 Delete", callback_data=f"draft:del:{draft_id}"),
        ],
        [InlineKeyboardButton("📋 My Drafts", callback_data="panel:drafts")],
    ]
    if count > 0 and bot_username:
        practice = ensure_practice_link(draft_id, int(draft["owner_id"]))
        practice_url = f"https://t.me/{bot_username}?start=practice_{practice['token']}"
        kb_rows.insert(1, [InlineKeyboardButton("🧪 Practice Link", url=practice_url)])
    kb = InlineKeyboardMarkup(kb_rows)
    await context.bot.send_message(chat_id, text, parse_mode=ParseMode.HTML, reply_markup=kb, disable_web_page_preview=True)


async def notify_admins(context: ContextTypes.DEFAULT_TYPE, text: str) -> None:
    for uid in all_admin_ids():
        row = DBH.fetchone("SELECT started FROM known_users WHERE user_id=?", (uid,))
        if row and int(row["started"]) == 1:
            with suppress(TelegramError):
                await context.bot.send_message(uid, text, parse_mode=ParseMode.HTML)


async def start_exam_countdown(context: ContextTypes.DEFAULT_TYPE, session_id: str, existing_message_id: Optional[int] = None) -> None:
    session = get_session(session_id)
    if not session:
        return
    chat_id = int(session["chat_id"])
    countdown = CONFIG.countdown_seconds

    def build_text(sec: int, starting: bool = False) -> str:
        lines = [
            f"<b>{html_escape(session['title'])}</b>",
            f"Questions: <b>{session['total_questions']}</b>",
            f"Time / question: <b>{session['question_time']} sec</b>",
            f"Negative / wrong: <b>{session['negative_mark']}</b>",
        ]
        if starting:
            lines.append("\n<b>Exam starting now…</b>")
        else:
            lines.append(f"\nStart countdown: <b>{sec}</b> sec")
        return "\n".join(lines)

    msg = None
    if existing_message_id:
        with suppress(TelegramError):
            await context.bot.edit_message_text(chat_id=chat_id, message_id=existing_message_id, text=build_text(countdown), parse_mode=ParseMode.HTML, reply_markup=None)
        class _M: pass
        msg = _M()
        msg.message_id = existing_message_id
    else:
        msg = await context.bot.send_message(chat_id, build_text(countdown), parse_mode=ParseMode.HTML)
        await safe_pin_message(context.bot, chat_id, msg.message_id)
        await delete_service_pin_later(context, chat_id)
    mark_session_countdown_message(session_id, msg.message_id)

    for sec in range(countdown - 1, 0, -1):
        await asyncio.sleep(1)
        current = get_session(session_id)
        if not current or current["status"] != "countdown":
            return
        with suppress(TelegramError):
            await context.bot.edit_message_text(chat_id=chat_id, message_id=msg.message_id, text=build_text(sec), parse_mode=ParseMode.HTML)
    await asyncio.sleep(1)
    current = get_session(session_id)
    if not current or current["status"] != "countdown":
        return
    with suppress(TelegramError):
        await context.bot.edit_message_text(chat_id=chat_id, message_id=msg.message_id, text=build_text(0, starting=True), parse_mode=ParseMode.HTML)
    DBH.execute("UPDATE sessions SET status='running', status_message_id=? WHERE id=?", (msg.message_id, session_id))
    context.job_queue.run_once(begin_or_advance_exam_job, when=0.4, data={"session_id": session_id}, name=f"advance:{session_id}")


async def begin_or_advance_exam_job(context: ContextTypes.DEFAULT_TYPE) -> None:
    session_id = context.job.data["session_id"]
    await begin_or_advance_exam(context, session_id)


async def begin_or_advance_exam(context: ContextTypes.DEFAULT_TYPE, session_id: str) -> None:
    session = get_session(session_id)
    if not session or session["status"] != "running":
        return
    next_index = int(session["current_index"]) + 1
    total = int(session["total_questions"])
    if next_index > total:
        await finish_exam(context, session_id, reason="completed")
        return
    q = get_session_question(session_id, next_index)
    if not q:
        await finish_exam(context, session_id, reason="missing_question")
        return
    options = jload(q["options"], []) or []
    try:
        question_prefix = f"[{next_index}/{total}] [{session['title']}]\n"
        poll_question = (question_prefix + q["question"]).strip()
        if len(poll_question) > 300:
            allowed_q = max(10, 300 - len(question_prefix))
            poll_question = question_prefix + q["question"][:allowed_q - 1].rstrip() + "…"
        explanation_text = q["explanation"] or f"Question {next_index} of {total}"
        if len(explanation_text) > 200:
            explanation_text = explanation_text[:199] + "…"
        msg = await context.bot.send_poll(
            chat_id=session["chat_id"],
            question=poll_question,
            options=options,
            type=Poll.QUIZ,
            is_anonymous=False,
            allows_multiple_answers=False,
            correct_option_id=int(q["correct_option"]),
            explanation=explanation_text,
            open_period=max(5, int(session["question_time"])),
        )
    except TelegramError as exc:
        logger.exception("Failed to send poll: %s", exc)
        await finish_exam(context, session_id, reason="send_poll_error")
        return

    poll_id = msg.poll.id
    with closing(DBH.connect()) as conn:
        conn.execute(
            "UPDATE session_questions SET poll_id=?, message_id=?, open_ts=?, close_ts=? WHERE session_id=? AND q_no=?",
            (poll_id, msg.message_id, now_ts(), now_ts() + int(session["question_time"]), session_id, next_index),
        )
        conn.execute(
            "UPDATE sessions SET current_index=?, active_poll_id=?, active_poll_message_id=? WHERE id=?",
            (next_index, poll_id, msg.message_id, session_id),
        )
        conn.commit()
    context.job_queue.run_once(close_poll_job, when=max(1, int(session["question_time"])), data={"session_id": session_id, "q_no": next_index}, name=f"close:{session_id}:{next_index}")


async def close_poll_job(context: ContextTypes.DEFAULT_TYPE) -> None:
    session_id = context.job.data["session_id"]
    q_no = context.job.data["q_no"]
    session = get_session(session_id)
    if not session or session["status"] != "running":
        return
    q = get_session_question(session_id, q_no)
    if not q:
        return
    # Poll already auto-closes because send_poll uses open_period.
    set_session_active_poll(session_id, None, None)
    context.job_queue.run_once(begin_or_advance_exam_job, when=0.8, data={"session_id": session_id}, name=f"advance:{session_id}")


async def finish_exam(context: ContextTypes.DEFAULT_TYPE, session_id: str, reason: str = "completed") -> None:
    session = get_session(session_id)
    if not session or session["status"] in {"finished", "stopped"}:
        return
    chat_id = int(session["chat_id"])
    chat_row = DBH.fetchone("SELECT chat_type FROM known_chats WHERE chat_id=?", (chat_id,))
    chat_type = (chat_row["chat_type"] if chat_row else "") or ""
    is_private_exam = chat_type == "private"

    for prefix in (f"close:{session_id}:", f"advance:{session_id}"):
        for job in context.job_queue.jobs():
            if job.name and job.name.startswith(prefix):
                job.schedule_removal()

    DBH.execute(
        "UPDATE sessions SET status=?, ended_at=?, active_poll_id=NULL, active_poll_message_id=NULL WHERE id=?",
        ("finished" if reason == "completed" else "stopped", now_ts(), session_id),
    )
    ranking = get_session_ranking(session_id)
    top = ranking[: CONFIG.scoreboard_top_n]
    leaderboard_rows = [{"name": item["name"], "sub": item.get("sub_name", ""), "score": item["score"], "user_id": item.get("user_id")} for item in top]
    image_bytes = render_leaderboard_png(session["title"], leaderboard_rows or [{"name": "No eligible participants", "sub": "", "score": "0.00"}])

    try:
        await context.bot.send_chat_action(chat_id=chat_id, action=ChatAction.UPLOAD_PHOTO)
        await context.bot.send_photo(chat_id=chat_id, photo=InputFile(io.BytesIO(image_bytes), filename="leaderboard.png"), caption=f"🏁 {session['title']} finished.")
    except TelegramError as exc:
        logger.warning("Could not send leaderboard image for %s: %s", session_id, exc)

    try:
        await send_private_results(context, session_id)
    except Exception:
        logger.exception("Failed to send private results for %s", session_id)

    if not is_private_exam:
        try:
            await send_admin_pdf_report(context, session_id, ranking)
        except Exception:
            logger.exception("Failed to send admin PDF report for %s", session_id)

    if not is_private_exam:
        DBH.execute("DELETE FROM group_bindings WHERE chat_id=?", (chat_id,))
        draft = get_draft(session["draft_id"])
        if draft:
            delete_draft(draft["id"], int(session["created_by"]))

    retention_ts = now_ts() + (CONFIG.retention_hours * 3600)
    queue_delete("session", session_id, retention_ts)
    audit(int(session["created_by"]), "finish_exam", session_id, {"reason": reason, "participants": len(ranking)})


async def send_admin_pdf_report(context: ContextTypes.DEFAULT_TYPE, session_id: str, ranking: List[Dict[str, Any]]) -> None:
    session = get_session(session_id)
    if not session:
        return
    rows = DBH.fetchall("SELECT score FROM participants WHERE session_id=? AND eligible=1", (session_id,))
    scores = [float(r["score"]) for r in rows] or [0.0]
    qstats = get_question_analytics(session_id)
    summary = {
        "participants": len(ranking),
        "questions": int(session["total_questions"]),
        "average_score": fmt_score(sum(scores) / len(scores)),
        "highest_score": fmt_score(max(scores)),
        "lowest_score": fmt_score(min(scores)),
        "negative_mark": session["negative_mark"],
        "started_at": fmt_dt(session["started_at"]),
        "ended_at": fmt_dt(session["ended_at"]),
    }
    pdf_bytes = render_report_pdf(session["title"], summary, ranking, qstats)
    recipients: List[int] = []
    for uid in [int(session["created_by"])] + list(CONFIG.owner_ids) + all_admin_ids():
        if uid not in recipients:
            recipients.append(uid)
    logger.info("Sending PDF report for %s to recipients=%s", session_id, recipients)
    sent_any = False
    for uid in recipients:
        try:
            await context.bot.send_document(
                uid,
                document=InputFile(io.BytesIO(pdf_bytes), filename=f"{pdf_safe_filename(session['title'])}_report.pdf"),
                caption=f"📄 {session['title']} report",
            )
            sent_any = True
        except TelegramError as exc:
            logger.warning("Could not send PDF report to %s: %s", uid, exc)
    if not sent_any:
        logger.warning("PDF report for %s was not delivered to any recipient", session_id)


async def send_private_results(context: ContextTypes.DEFAULT_TYPE, session_id: str) -> None:
    session = get_session(session_id)
    if not session:
        return
    chat_row = DBH.fetchone("SELECT username, chat_type FROM known_chats WHERE chat_id=?", (session["chat_id"],))
    username = chat_row["username"] if chat_row else None
    ranking = get_session_ranking(session_id)
    rank_map = {r["user_id"]: r for r in ranking}
    qrows = DBH.fetchall("SELECT q_no, message_id, question FROM session_questions WHERE session_id=? ORDER BY q_no", (session_id,))
    q_map = {int(r["q_no"]): r for r in qrows}
    participants = DBH.fetchall("SELECT * FROM participants WHERE session_id=? AND eligible=1", (session_id,))
    for p in participants:
        row = DBH.fetchone("SELECT started FROM known_users WHERE user_id=?", (p["user_id"],))
        if not row or int(row["started"]) != 1:
            continue
        rank_item = rank_map.get(int(p["user_id"]))
        if not rank_item:
            continue
        if not await is_required_channel_member(context, int(p["user_id"])):
            continue
        answers = DBH.fetchall("SELECT * FROM answers WHERE session_id=? AND user_id=? ORDER BY q_no", (session_id, p["user_id"]))
        answer_by_q = {int(a["q_no"]): a for a in answers}
        correct_links: List[str] = []
        wrong_links: List[str] = []
        skipped_links: List[str] = []
        for q_no, q in q_map.items():
            link = get_message_link(int(session["chat_id"]), int(q["message_id"] or 0), username)
            anchor = f"Q{q_no}"
            label = f"<a href=\"{link}\">{anchor}</a>" if link else anchor
            ans = answer_by_q.get(q_no)
            if ans is None:
                skipped_links.append(label)
            elif int(ans["is_correct"]) == 1:
                correct_links.append(label)
            else:
                wrong_links.append(label)
        text = (
            f"<b>{html_escape(session['title'])}</b>\n"
            f"Your rank: <b>#{rank_item['rank']}</b>\n"
            f"✅ Correct: <b>{rank_item['correct']}</b>\n"
            f"❌ Wrong: <b>{rank_item['wrong']}</b>\n"
            f"➖ Skipped: <b>{rank_item['skipped']}</b>\n"
            f"🏁 Final Score: <b>{rank_item['score']}</b>\n\n"
            f"<b>Correct Links</b>\n{', '.join(correct_links) or '—'}\n\n"
            f"<b>Wrong Links</b>\n{', '.join(wrong_links) or '—'}\n\n"
            f"<b>Skipped Links</b>\n{', '.join(skipped_links) or '—'}"
        )
        with suppress(TelegramError):
            await context.bot.send_message(
                chat_id=p["user_id"],
                text=text,
                parse_mode=ParseMode.HTML,
                link_preview_options=LinkPreviewOptions(is_disabled=True),
            )


async def cleanup_old_data_job(context: ContextTypes.DEFAULT_TYPE) -> None:
    rows = DBH.fetchall("SELECT * FROM delete_queue WHERE delete_after <= ?", (now_ts(),))
    for row in rows:
        if row["kind"] == "session":
            cleanup_session_data(row["ref_id"])
        DBH.execute("DELETE FROM delete_queue WHERE ref_id=?", (row["ref_id"],))
    stale_states_before = now_ts() - 86400
    DBH.execute("DELETE FROM user_state WHERE updated_at < ?", (stale_states_before,))

# ============================================================
# UI helpers
# ============================================================


def panel_keyboard(is_owner_user: bool) -> InlineKeyboardMarkup:
    rows = [
        [InlineKeyboardButton("➕ New Exam", callback_data="panel:new"), InlineKeyboardButton("📚 My Drafts", callback_data="panel:drafts")],
        [InlineKeyboardButton("🧭 Known Groups", callback_data="panel:groups"), InlineKeyboardButton("⏰ My Schedules", callback_data="panel:schedules")],
        [InlineKeyboardButton("▶️ Start Exam", callback_data="panel:start_exam"), InlineKeyboardButton("🛑 Stop Exam", callback_data="panel:stop_exam")],
        [InlineKeyboardButton("📘 Commands", callback_data="panel:commands")],
    ]
    if is_owner_user:
        rows.append([InlineKeyboardButton("👥 Admins", callback_data="panel:admins"), InlineKeyboardButton("📋 Logs", callback_data="panel:logs")])
        rows.append([InlineKeyboardButton("📢 Broadcast Help", callback_data="panel:broadcast")])
    return InlineKeyboardMarkup(rows)


def panel_back_keyboard(is_owner_user: bool) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup([[InlineKeyboardButton("⬅️ Back", callback_data="panel:home")]])


async def panel_show_message(message: Message, user_id: int, text: str, reply_markup=None) -> None:
    if not message:
        return
    with suppress(TelegramError):
        await message.edit_text(text, parse_mode=ParseMode.HTML, reply_markup=reply_markup, disable_web_page_preview=True)
        return
    with suppress(TelegramError):
        await message.reply_text(text, parse_mode=ParseMode.HTML, reply_markup=reply_markup, disable_web_page_preview=True)


async def send_panel(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    user = update.effective_user
    if not user:
        return
    text = (
        f"<b>{CONFIG.brand_name}</b>\n\n"
        f"এই bot এ exam draft তৈরি, quiz forward/import, start/stop, schedule, leaderboard image, PDF report, DM result, logs, broadcast—সব আছে।\n\n"
        f"<b>Quick flow</b>\n"
        f"1) New Exam\n"
        f"2) Quiz forward / CSV upload\n"
        f"3) Panel থেকে draft active করুন\n"
        f"4) Group-এ <code>.starttqex</code> বা <code>.starttqex DRAFTCODE</code> দিন\n"
        f"5) Draft card থেকে practice link share করতে পারবেন\n"
        f"6) চাইলে <code>.schedule YYYY-MM-DD HH:MM</code>\n\n"
        f"সব group command <b>/</b> এবং <b>.</b> — দুই prefix এই কাজ করবে।"
    )
    await context.bot.send_message(user.id, text, parse_mode=ParseMode.HTML, reply_markup=panel_keyboard(is_owner(user.id)), disable_web_page_preview=True)


async def show_groups(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    user = update.effective_user
    if not user or not is_owner(user.id):
        await context.bot.send_message(user.id if user else update.effective_chat.id, warning_text())
        return
    rows = DBH.fetchall("SELECT * FROM known_chats WHERE active=1 AND chat_type IN ('group','supergroup') ORDER BY title COLLATE NOCASE ASC")
    if not rows:
        text = "কোনো known group এখনও নেই। Bot-কে আগে group-এ add করুন।"
    else:
        lines = ["<b>Known Groups</b>"]
        for row in rows[:50]:
            lines.append(f"• <b>{html_escape(row['title'])}</b> — <code>{row['chat_id']}</code>")
        text = "\n".join(lines)
    target = user.id if user else update.effective_chat.id
    await context.bot.send_message(target, text, parse_mode=ParseMode.HTML)


async def show_drafts(update: Update, context: ContextTypes.DEFAULT_TYPE, user_id: int) -> None:
    drafts = list_user_drafts(user_id)
    if not drafts:
        await context.bot.send_message(user_id, "আপনার কোনো draft নেই। প্রথমে New Exam দিন।")
        return
    lines = ["<b>Your Drafts</b>"]
    kb_rows = []
    for row in drafts[:12]:
        lines.append(
            f"• <b>{html_escape(row['title'])}</b> — <code>{row['id']}</code> | Q: {row['q_count']} | {row['question_time']}s | -{row['negative_mark']}"
        )
        kb_rows.append([InlineKeyboardButton(f"Use {row['id']}", callback_data=f"draft:set:{row['id']}")])
    await context.bot.send_message(user_id, "\n".join(lines), parse_mode=ParseMode.HTML, reply_markup=InlineKeyboardMarkup(kb_rows[:10]) if kb_rows else None)


async def show_admins(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    lines = ["<b>Owners</b>"]
    for oid in CONFIG.owner_ids:
        lines.append(f"• <code>{oid}</code>")
    rows = DBH.fetchall("SELECT * FROM bot_admins ORDER BY added_at DESC")
    lines.append("\n<b>Bot Admins</b>")
    if not rows:
        lines.append("• None")
    for r in rows:
        lines.append(f"• <code>{r['user_id']}</code> (added {fmt_dt(r['added_at'])})")
    target = update.effective_user.id if update.effective_user else update.effective_chat.id
    await context.bot.send_message(target, "\n".join(lines), parse_mode=ParseMode.HTML)


async def show_logs(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    proc = psutil.Process(os.getpid())
    rss_mb = proc.memory_info().rss / (1024 * 1024)
    uptime = fmt_duration(time.time() - START_TS)
    error_lines: List[str] = []
    one_hour_ago = time.time() - 3600
    if LOG_FILE.exists():
        with LOG_FILE.open("r", encoding="utf-8", errors="ignore") as fh:
            for line in fh.readlines()[-500:]:
                if " | ERROR | " not in line and " | CRITICAL | " not in line:
                    continue
                try:
                    stamp = line.split(" | ", 1)[0]
                    dt_obj = datetime.strptime(stamp, "%Y-%m-%d %H:%M:%S,%f").replace(tzinfo=TZ)
                    if dt_obj.timestamp() >= one_hour_ago:
                        error_lines.append(line.strip())
                except Exception:
                    error_lines.append(line.strip())
    text = (
        f"<b>Bot Logs Summary</b>\n"
        f"Memory: <b>{rss_mb:.2f} MB</b>\n"
        f"Uptime: <b>{uptime}</b>\n"
        f"Errors in last hour: <b>{len(error_lines)}</b>\n\n"
        f"<b>Recent Errors</b>\n"
        + ("\n".join(html_escape(x) for x in error_lines[:10]) if error_lines else "No error in last hour.")
    )
    user_id = update.effective_user.id if update.effective_user else None
    if user_id:
        await context.bot.send_message(user_id, text, parse_mode=ParseMode.HTML)
        if LOG_FILE.exists():
            with LOG_FILE.open("rb") as fh:
                await context.bot.send_document(user_id, document=InputFile(fh, filename="bot.log"), caption="Full log file")


async def show_audit(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    rows = DBH.fetchall("SELECT * FROM audit_logs ORDER BY id DESC LIMIT 25")
    if not rows:
        await context.bot.send_message(update.effective_user.id, "No audit log yet.")
        return
    lines = ["<b>Recent Admin Actions</b>"]
    for r in rows:
        lines.append(
            f"• {fmt_dt(r['created_at'])} — <code>{r['actor_id']}</code> — <b>{html_escape(r['action'])}</b> — {html_escape(r['target'] or '—')}"
        )
    await context.bot.send_message(update.effective_user.id, "\n".join(lines), parse_mode=ParseMode.HTML)


# ============================================================
# Handlers
# ============================================================

async def handle_my_chat_member(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    cmu = update.my_chat_member
    if not cmu:
        return
    chat = cmu.chat
    record_chat(chat)
    new_status = cmu.new_chat_member.status
    active = 1 if new_status not in {ChatMemberStatus.LEFT, ChatMemberStatus.KICKED} else 0
    DBH.execute("UPDATE known_chats SET active=?, last_seen=? WHERE chat_id=?", (active, now_ts(), chat.id))


async def handle_pinned_service(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    message = update.effective_message
    chat = update.effective_chat
    if not message or not chat:
        return
    pin_cleanup = context.bot_data.setdefault("pin_cleanup_until", {})
    until = pin_cleanup.get(chat.id, 0)
    if until >= now_ts():
        await safe_delete_message(context.bot, chat.id, message.message_id)
        if now_ts() > until:
            pin_cleanup.pop(chat.id, None)


async def callback_router(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    if not query or not query.data:
        return
    await query.answer()
    data = query.data
    user = query.from_user
    record_user(user)

    if data.startswith("startready:"):
        with suppress(Exception):
            chat_id = int(data.split(":", 1)[1])
            ready_store = context.bot_data.setdefault("ready_starts", {})
            state = ready_store.get(chat_id)
            if not state:
                await query.answer("এই start request আর active নেই।", show_alert=False)
                return
            users = state.setdefault("users", [])
            if user.id not in users:
                users.append(user.id)
            count = len(users)
            text = (
                f"<b>{html_escape(state['title'])}</b>\n"
                f"Questions: <b>{state['questions']}</b>\n"
                f"Time / question: <b>{state['question_time']} sec</b>\n"
                f"Negative / wrong: <b>{state['negative_mark']}</b>\n\n"
                f"Exam will start when at least <b>2 users</b> press the ready button.\n"
                f"Ready now: <b>{count}/2</b>"
            )
            kb = InlineKeyboardMarkup([[InlineKeyboardButton("✅ Start Exam", callback_data=f"startready:{chat_id}")]]) if count < 2 else None
            with suppress(TelegramError):
                await query.message.edit_text(text, parse_mode=ParseMode.HTML, reply_markup=kb)
            if count < 2:
                await query.answer(f"Ready recorded: {count}/2", show_alert=False)
                return
            if get_active_session(chat_id):
                ready_store.pop(chat_id, None)
                await query.answer("এই group এ exam already চলছে।", show_alert=False)
                return
            session_id = create_session_from_draft(state['draft_id'], chat_id, int(state['requested_by']))
            ready_store.pop(chat_id, None)
            if not session_id:
                await query.answer("Session create করা যায়নি।", show_alert=True)
                return
            await query.answer("Exam starting...", show_alert=False)
            await start_exam_countdown(context, session_id, existing_message_id=query.message.message_id if query.message else None)
            return

    if not user_has_staff_access(user.id):
        await panel_show_message(query.message, user.id, warning_text(), reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("📘 Commands", callback_data="panel:commands")]]))
        return

    async def show_page(text: str, reply_markup=None):
        await panel_show_message(query.message, user.id, text, reply_markup=reply_markup)

    if data == "panel:home":
        text = (
            f"<b>{CONFIG.brand_name}</b>\n\n"
            f"এই bot এ exam draft তৈরি, quiz forward/import, start/stop, schedule, leaderboard image, PDF report, DM result, logs, broadcast—সব আছে।\n\n"
            f"<b>Quick flow</b>\n"
            f"1) New Exam\n2) Quiz forward / CSV upload\n3) Active draft নির্বাচন\n4) Group-এ start/schedule\n\n"
            f"সব group command <b>/</b> এবং <b>.</b> — দুই prefix এই কাজ করবে।"
        )
        await show_page(text, panel_keyboard(is_owner(user.id)))
        return
    if data == "panel:new":
        set_user_state(user.id, "await_title")
        await show_page("<b>New Exam</b>\n\nExam title পাঠান।", panel_back_keyboard(is_owner(user.id)))
        return
    if data == "panel:drafts":
        drafts = list_user_drafts(user.id)
        if not drafts:
            await show_page("আপনার কোনো draft নেই। প্রথমে New Exam দিন।", panel_back_keyboard(is_owner(user.id)))
            return
        lines = ["<b>Your Drafts</b>"]
        kb_rows = []
        for row in drafts[:12]:
            lines.append(f"• <b>{html_escape(row['title'])}</b> — <code>{row['id']}</code> | Q: {row['q_count']} | {row['question_time']}s | -{row['negative_mark']}")
            kb_rows.append([InlineKeyboardButton(f"✅ Active {row['id']}", callback_data=f"draft:set:{row['id']}"), InlineKeyboardButton("🗑", callback_data=f"draft:del:{row['id']}")])
        kb_rows.append([InlineKeyboardButton("⬅️ Back", callback_data="panel:home")])
        await show_page("\n".join(lines), InlineKeyboardMarkup(kb_rows[:11]))
        return
    if data == "panel:groups":
        rows = DBH.fetchall("SELECT * FROM known_chats WHERE active=1 AND chat_type IN ('group','supergroup') ORDER BY title COLLATE NOCASE ASC")
        if not rows:
            text = "কোনো known group এখনও নেই। Bot-কে আগে group-এ add করুন।"
        else:
            lines = ["<b>Known Groups</b>"]
            for row in rows[:50]:
                lines.append(f"• <b>{html_escape(row['title'])}</b> — <code>{row['chat_id']}</code>")
            text = "\n".join(lines)
        await show_page(text, panel_back_keyboard(is_owner(user.id)))
        return
    if data == "panel:schedules":
        rows = DBH.fetchall("SELECT s.*, d.title FROM schedules s JOIN drafts d ON d.id=s.draft_id WHERE s.status='scheduled' ORDER BY s.run_at ASC LIMIT 20")
        if not rows:
            text = "কোন scheduled exam নেই।"
        else:
            lines = ["<b>Scheduled Exams</b>"]
            for row in rows:
                lines.append(f"• <code>{row['id']}</code> — {html_escape(row['title'])} — {fmt_dt(row['run_at'])} — chat <code>{row['chat_id']}</code>")
            text = "\n".join(lines)
        await show_page(text, panel_back_keyboard(is_owner(user.id)))
        return
    if data == "panel:admins":
        if not is_owner(user.id):
            await show_page("Only owner can view admins.", panel_back_keyboard(is_owner(user.id)))
            return
        lines = ["<b>Owners</b>"]
        for oid in CONFIG.owner_ids:
            lines.append(f"• <code>{oid}</code>")
        rows = DBH.fetchall("SELECT * FROM bot_admins ORDER BY added_at DESC")
        lines.append("\n<b>Bot Admins</b>")
        if not rows:
            lines.append("• None")
        for r in rows:
            lines.append(f"• <code>{r['user_id']}</code> (added {fmt_dt(r['added_at'])})")
        await show_page("\n".join(lines), panel_back_keyboard(is_owner(user.id)))
        return
    if data == "panel:logs":
        if not is_owner(user.id):
            await show_page("Only owner can view logs.", panel_back_keyboard(is_owner(user.id)))
            return
        proc = psutil.Process(os.getpid())
        rss_mb = proc.memory_info().rss / (1024 * 1024)
        uptime = fmt_duration(time.time() - START_TS)
        error_lines = []
        one_hour_ago = time.time() - 3600
        if LOG_FILE.exists():
            with LOG_FILE.open("r", encoding="utf-8", errors="ignore") as fh:
                for line in fh.readlines()[-500:]:
                    if " | ERROR | " not in line and " | CRITICAL | " not in line:
                        continue
                    try:
                        stamp = line.split(" | ", 1)[0]
                        dt_obj = datetime.strptime(stamp, "%Y-%m-%d %H:%M:%S,%f").replace(tzinfo=TZ)
                        if dt_obj.timestamp() >= one_hour_ago:
                            error_lines.append(line.strip())
                    except Exception:
                        error_lines.append(line.strip())
        text = (f"<b>Bot Logs Summary</b>\nMemory: <b>{rss_mb:.2f} MB</b>\nUptime: <b>{uptime}</b>\nErrors in last hour: <b>{len(error_lines)}</b>\n\n<b>Recent Errors</b>\n" + ("\n".join(html_escape(x) for x in error_lines[:10]) if error_lines else "No error in last hour."))
        await show_page(text, panel_back_keyboard(is_owner(user.id)))
        return
    if data == "panel:broadcast":
        if not is_owner(user.id):
            return
        text = ("Reply to any message in your PM with:\n<code>/broadcast</code> or <code>.broadcast</code> → all groups + started users\n<code>/broadcast pin</code> → groups only pin too\n<code>/announce CHAT_ID pin</code> → one target chat")
        await show_page(text, panel_back_keyboard(is_owner(user.id)))
        return
    if data == "panel:commands":
        text = build_commands_text("private", is_admin_user=is_bot_admin(user.id), is_owner_user=is_owner(user.id))
        await show_page(text, panel_back_keyboard(is_owner(user.id)))
        return
    if data == "panel:start_exam":
        draft_id = get_active_draft_id(user.id)
        rows = DBH.fetchall("SELECT * FROM known_chats WHERE active=1 AND chat_type IN ('group','supergroup') ORDER BY title COLLATE NOCASE ASC LIMIT 30")
        if not rows:
            await show_page("কোনো known group নেই। আগে bot-কে group-এ add করুন।", panel_back_keyboard(is_owner(user.id)))
            return
        if not draft_id:
            await show_page("আগে একটি active draft set করুন।", panel_back_keyboard(is_owner(user.id)))
            return
        draft = get_draft(draft_id)
        kb = []
        for row in rows[:20]:
            kb.append([InlineKeyboardButton(f"▶️ {row['title']}", callback_data=f"panel:startgroup:{row['chat_id']}")])
        kb.append([InlineKeyboardButton("⬅️ Back", callback_data="panel:home")])
        await show_page(f"<b>Start Exam</b>\nActive draft: <code>{draft_id}</code> — {html_escape(draft['title'] if draft else draft_id)}\n\nএকটি group বাছাই করুন:", InlineKeyboardMarkup(kb))
        return
    if data.startswith("panel:startgroup:"):
        chat_id = int(data.split(":", 2)[2])
        draft_id = get_active_draft_id(user.id)
        if not draft_id:
            await show_page("আগে active draft set করুন।", panel_back_keyboard(is_owner(user.id)))
            return
        if get_active_session(chat_id):
            await show_page("এই group-এ আগে থেকেই exam চলছে।", panel_back_keyboard(is_owner(user.id)))
            return
        bind_draft_to_group(draft_id, chat_id, user.id)
        session_id = create_session_from_draft(draft_id, chat_id, user.id)
        if not session_id:
            await show_page("Session create করা যায়নি। Draft-এ প্রশ্ন আছে কি না দেখুন।", panel_back_keyboard(is_owner(user.id)))
            return
        await start_exam_countdown(context, session_id)
        draft = get_draft(draft_id)
        await show_page(f"✅ Started <b>{html_escape(draft['title'] if draft else draft_id)}</b> in <code>{chat_id}</code>", panel_back_keyboard(is_owner(user.id)))
        return
    if data == "panel:stop_exam":
        rows = DBH.fetchall("SELECT * FROM sessions WHERE status IN ('countdown','running') ORDER BY started_at DESC LIMIT 20")
        if not rows:
            await show_page("কোন active exam নেই।", panel_back_keyboard(is_owner(user.id)))
            return
        kb = []
        lines = ["<b>Running Exams</b>"]
        for row in rows:
            lines.append(f"• <b>{html_escape(row['title'])}</b> — chat <code>{row['chat_id']}</code> — Q {row['current_index']}/{row['total_questions']}")
            kb.append([InlineKeyboardButton(f"🛑 Stop {row['chat_id']}", callback_data=f"panel:stopsession:{row['id']}")])
        kb.append([InlineKeyboardButton("⬅️ Back", callback_data="panel:home")])
        await show_page("\n".join(lines), InlineKeyboardMarkup(kb[:21]))
        return
    if data.startswith("panel:stopsession:"):
        session_id = data.split(":", 2)[2]
        session = get_session(session_id)
        if not session:
            await show_page("Session পাওয়া যায়নি।", panel_back_keyboard(is_owner(user.id)))
            return
        await finish_exam(context, session_id, reason="manual_stop")
        await show_page(f"🛑 Stopped <b>{html_escape(session['title'])}</b> in chat <code>{session['chat_id']}</code>", panel_back_keyboard(is_owner(user.id)))
        return
    if data.startswith("draft:set:"):
        draft_id = data.split(":", 2)[2]
        draft = get_draft(draft_id)
        if not draft or int(draft["owner_id"]) != user.id:
            await show_page("এই draft পাওয়া যায়নি।", panel_back_keyboard(is_owner(user.id)))
            return
        set_active_draft(user.id, draft_id)
        text = (
            f"✅ <b>Active Draft Updated</b>\n\n"
            f"<b>Draft:</b> {html_escape(draft['title'])}\n"
            f"<b>Code:</b> <code>{draft['id']}</code>\n"
            f"এখন quiz forward করুন, CSV upload করুন, অথবা Panel → Start Exam ব্যবহার করুন।"
        )
        await show_page(text, panel_back_keyboard(is_owner(user.id)))
        return
    if data.startswith("draft:del:"):
        draft_id = data.split(":", 2)[2]
        draft = get_draft(draft_id)
        if not draft:
            await show_page("Draft already deleted.", panel_back_keyboard(is_owner(user.id)))
            return
        if int(draft["owner_id"]) != user.id and not is_owner(user.id):
            await show_page("এই draft delete করার অনুমতি নেই।", panel_back_keyboard(is_owner(user.id)))
            return
        delete_draft(draft_id, user.id)
        await show_page("🗑 Draft deleted.", panel_back_keyboard(is_owner(user.id)))
        return


async def handle_text(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if update.edited_message:
        return
    message = update.effective_message
    user = update.effective_user
    chat = update.effective_chat
    if not message or not user or not chat or not message.text:
        return
    record_user(user)
    record_chat(chat)

    command, args = extract_command(message.text, context.bot_data.get("bot_username", ""))

    # Private state flow for admin/owner
    state, payload = get_user_state(user.id)
    if chat.type == "private" and state and not command:
        if state == "await_title":
            payload = {"title": message.text.strip()}
            set_user_state(user.id, "await_qtime", payload)
            await safe_reply(message, "প্রতি প্রশ্নের সময় (seconds) পাঠান। উদাহরণ: 30")
            return
        if state == "await_qtime":
            if not message.text.strip().isdigit() or int(message.text.strip()) <= 0:
                await safe_reply(message, "ভ্যালিড positive number দিন।")
                return
            payload["question_time"] = int(message.text.strip())
            set_user_state(user.id, "await_negative", payload)
            await safe_reply(message, "Negative mark per wrong answer দিন। উদাহরণ: 0.25")
            return
        if state == "await_negative":
            try:
                neg = float(message.text.strip())
            except ValueError:
                await safe_reply(message, "ভ্যালিড decimal number দিন।")
                return
            title = payload["title"]
            qtime = int(payload["question_time"])
            draft_id = create_draft(user.id, title, qtime, neg)
            clear_user_state(user.id)
            await send_draft_card(context, user.id, user.id, draft_id, header="✅ New exam draft created")
            return

    if not command:
        return

    # universal private /start with join gate + deep-link practice
    if command == "start":
        mark_started(user)
        if chat.type == "private":
            joined = await is_required_channel_member(context, user.id)
            if not joined:
                kb = InlineKeyboardMarkup([[InlineKeyboardButton("Join Required Channel", url=f"https://t.me/{CONFIG.required_channel.lstrip('@')}")]])
                await safe_reply(message, f"এই bot ব্যবহার করতে আগে {CONFIG.required_channel} channel এ join করুন। তারপর আবার /start দিন।", reply_markup=kb)
                return
            if args.strip().startswith("practice_"):
                await start_practice_from_token(update, context, args.strip()[9:])
                return
            await send_panel(update, context)
        else:
            await handle_group_denied_command(update, context, "Private এ /start দিয়ে bot activate করুন।")
        return

    if command in {"cancel", "cancelstate"}:
        clear_user_state(user.id)
        await safe_reply(message, "চলমান input flow cancel করা হয়েছে।")
        return

    if command in {"help", "commands", "cmds"}:
        await send_commands_text(message, context)
        return

    if chat.type == "private" and command == "csvformat":
        if is_bot_admin(user.id):
            await send_csv_format_help(message)
        return

    # owner/admin PM commands
    if chat.type == "private" and not user_has_staff_access(user.id) and command not in {"start", "help", "commands", "cmds", "cancel", "cancelstate", "panel"}:
        await safe_reply(message, warning_text())
        return
    if chat.type == "private" and command == "panel":
        if user_has_staff_access(user.id):
            await send_panel(update, context)
        else:
            await safe_reply(message, warning_text())
        return

    if chat.type == "private" and command == "newexam":
        if not is_bot_admin(user.id):
            await safe_reply(message, "শুধু owner/admin exam তৈরি করতে পারবে।")
            return
        set_user_state(user.id, "await_title")
        await safe_reply(message, "Exam title পাঠান।")
        return

    if chat.type == "private" and command in {"mydrafts", "drafts"}:
        if not user_has_staff_access(user.id):
            await safe_reply(message, warning_text())
            return
        await show_drafts(update, context, user.id)
        return

    if command == "addadmin":
        if not is_owner(user.id):
            await safe_reply(message, "Only owner can add bot admin.")
            return
        target_id: Optional[int] = None
        if message.reply_to_message and message.reply_to_message.from_user:
            target_id = message.reply_to_message.from_user.id
        elif args.strip().isdigit():
            target_id = int(args.strip())
        if not target_id:
            await safe_reply(message, "Reply to a user or pass numeric user id.")
            return
        if is_owner(target_id):
            await safe_reply(message, "Owner already has full access.")
            return
        DBH.execute("INSERT OR REPLACE INTO bot_admins(user_id, added_by, added_at) VALUES(?,?,?)", (target_id, user.id, now_ts()))
        audit(user.id, "add_admin", str(target_id))
        await safe_reply(message, f"✅ Added bot admin: <code>{target_id}</code>", parse_mode=ParseMode.HTML)
        return

    if command in {"rmadmin", "removeadmin", "deladmin"}:
        if not is_owner(user.id):
            await safe_reply(message, "Only owner can remove bot admin.")
            return
        target_id = None
        if message.reply_to_message and message.reply_to_message.from_user:
            target_id = message.reply_to_message.from_user.id
        elif args.strip().isdigit():
            target_id = int(args.strip())
        if not target_id:
            await safe_reply(message, "Reply to a user or pass numeric user id.")
            return
        DBH.execute("DELETE FROM bot_admins WHERE user_id=?", (target_id,))
        audit(user.id, "remove_admin", str(target_id))
        await safe_reply(message, f"✅ Removed bot admin: <code>{target_id}</code>", parse_mode=ParseMode.HTML)
        return

    if chat.type == "private" and command == "admins":
        if not is_owner(user.id):
            await safe_reply(message, "Only owner can view admin list.")
            return
        await show_admins(update, context)
        return

    if chat.type == "private" and command == "audit":
        if not is_owner(user.id):
            return
        await show_audit(update, context)
        return

    if command == "logs":
        if not is_owner(user.id):
            return
        await show_logs(update, context)
        return

    if chat.type == "private" and command == "restart":
        if not is_owner(user.id):
            await safe_reply(message, warning_text())
            return
        await safe_reply(message, "♻️ Restarting bot process...")
        audit(user.id, "restart_bot", "process")
        os.execl(sys.executable, sys.executable, *sys.argv)
        return

    if chat.type == "private" and command == "broadcast":
        if not is_owner(user.id):
            return
        pin_mode = args.strip().lower() == "pin"
        if message.reply_to_message:
            await perform_broadcast(context, owner_id=user.id, source_message=message.reply_to_message, pin=pin_mode)
            await safe_reply(message, "📢 Broadcast done.")
        elif args.strip():
            await perform_broadcast(context, owner_id=user.id, source_message=None, text=args.strip(), pin=pin_mode)
            await safe_reply(message, "📢 Broadcast done.")
        else:
            await safe_reply(message, "Reply to a message or send text with /broadcast.")
        return

    if chat.type == "private" and command == "announce":
        if not is_owner(user.id):
            return
        parts = args.split()
        if not parts:
            await safe_reply(message, "Usage: /announce CHAT_ID [pin] as reply or text")
            return
        try:
            target_chat = int(parts[0])
        except ValueError:
            await safe_reply(message, "First argument must be target chat id.")
            return
        pin_mode = any(p.lower() == "pin" for p in parts[1:])
        if message.reply_to_message:
            await perform_announce(context, owner_id=user.id, target_chat_id=target_chat, source_message=message.reply_to_message, pin=pin_mode)
        else:
            text = " ".join(parts[1:]).replace("pin", "").strip()
            if not text:
                await safe_reply(message, "Reply to a message or pass text.")
                return
            await perform_announce(context, owner_id=user.id, target_chat_id=target_chat, text=text, pin=pin_mode)
        await safe_reply(message, "✅ Announcement sent.")
        return

    # group commands
    if chat.type not in {"group", "supergroup"}:
        return

    if command and not await is_group_admin_or_global(update, context):
        await handle_group_denied_command(update, context)
        return

    if command == "binddraft":
        if not await is_group_admin_or_global(update, context):
            await safe_reply(message, "শুধু group admin / bot admin draft bind করতে পারবে।")
            return
        if get_active_session(chat.id):
            await safe_reply(message, "Exam চলাকালে নতুন draft bind করা যাবে না।")
            return
        draft_id = args.strip().upper()
        draft = get_draft(draft_id)
        if not draft:
            await safe_reply(message, "এই draft code পাওয়া যায়নি।")
            return
        q_count_row = DBH.fetchone("SELECT COUNT(*) AS c FROM draft_questions WHERE draft_id=?", (draft_id,))
        q_count = int(q_count_row["c"] if q_count_row else 0)
        if q_count == 0:
            await safe_reply(message, "এই draft এ এখনও কোনো প্রশ্ন নেই।")
            return
        bind_draft_to_group(draft_id, chat.id, user.id)
        await safe_reply(message, f"✅ Bound draft <code>{draft_id}</code> to this group. এখন <code>.starttqex</code> বা <code>.schedule YYYY-MM-DD HH:MM</code>", parse_mode=ParseMode.HTML)
        return

    if command == "examstatus":
        active = get_active_session(chat.id)
        bound = get_bound_draft(chat.id)
        lines = [f"<b>{html_escape(chat.title or 'Group')}</b>"]
        if bound:
            q_count = DBH.fetchone("SELECT COUNT(*) AS c FROM draft_questions WHERE draft_id=?", (bound['id'],))
            lines.append(f"Bound draft: <b>{html_escape(bound['title'])}</b> (<code>{bound['id']}</code>) | Questions: {q_count['c']}")
        else:
            lines.append("Bound draft: None")
        if active:
            lines.append(f"Active exam: <b>{html_escape(active['title'])}</b> | Status: {active['status']} | Q {active['current_index']}/{active['total_questions']}")
        else:
            lines.append("Active exam: None")
        await safe_reply(message, "\n".join(lines), parse_mode=ParseMode.HTML)
        return

    if command == "starttqex":
        if get_active_session(chat.id):
            await safe_reply(message, "এই group এ আগে থেকেই একটি exam চলছে।")
            return
        draft_code = args.strip().upper()
        draft = get_draft(draft_code) if draft_code else resolve_group_draft_for_actor(chat.id, user.id)
        if draft_code and draft and int(draft['owner_id']) not in OWNER_SET and int(draft['owner_id']) != user.id and user.id not in all_admin_ids():
            await safe_reply(message, "এই draft code আপনি ব্যবহার করতে পারবেন না।")
            return
        if not draft:
            await safe_reply(message, "আগে একটি ready draft active/bind করুন, অথবা .starttqex DRAFTCODE দিন।")
            return
        q_count_row = DBH.fetchone("SELECT COUNT(*) AS c FROM draft_questions WHERE draft_id=?", (draft['id'],))
        q_count = int(q_count_row['c'] if q_count_row else 0)
        ready_store = context.bot_data.setdefault('ready_starts', {})
        ready_store[chat.id] = {
            'draft_id': draft['id'],
            'requested_by': user.id,
            'title': draft['title'],
            'question_time': int(draft['question_time']),
            'negative_mark': float(draft['negative_mark']),
            'questions': q_count,
            'users': [],
            'message_id': None,
        }
        text = (
            f"<b>{html_escape(draft['title'])}</b>\n"
            f"Questions: <b>{q_count}</b>\n"
            f"Time / question: <b>{draft['question_time']} sec</b>\n"
            f"Negative / wrong: <b>{draft['negative_mark']}</b>\n\n"
            f"Exam will start when at least <b>2 users</b> press the ready button.\n"
            f"Ready now: <b>0/2</b>"
        )
        kb = InlineKeyboardMarkup([[InlineKeyboardButton("✅ Start Exam", callback_data=f"startready:{chat.id}")]])
        sent = await safe_reply(message, text, parse_mode=ParseMode.HTML, reply_markup=kb)
        if sent:
            ready_store[chat.id]['message_id'] = sent.message_id
            await safe_pin_message(context.bot, chat.id, sent.message_id)
            await delete_service_pin_later(context, chat.id)
        await safe_delete_message(context.bot, chat.id, message.message_id)
        return

    if command == "stoptqex":
        if not await is_group_admin_or_global(update, context):
            await safe_reply(message, "শুধু group admin / bot admin exam stop করতে পারবে।")
            return
        session = get_active_session(chat.id)
        if not session:
            await safe_reply(message, "এই group এ কোনো active exam নেই।")
            return
        await finish_exam(context, session["id"], reason="manual_stop")
        await safe_reply(message, "🛑 Exam stopped.")
        await safe_delete_message(context.bot, chat.id, message.message_id)
        return

    if command == "schedule":
        if not await is_group_admin_or_global(update, context):
            await safe_reply(message, "শুধু group admin / bot admin schedule করতে পারবে।")
            return
        bound = resolve_group_draft_for_actor(chat.id, user.id)
        if not bound:
            await safe_reply(message, "আগে একটি ready draft active/bind করুন।")
            return
        run_at = parse_schedule_input(args)
        if not run_at:
            await safe_reply(message, "Usage: .schedule YYYY-MM-DD HH:MM")
            return
        if run_at <= now_ts() + 10:
            await safe_reply(message, "কমপক্ষে 10 সেকেন্ড পরের সময় দিন।")
            return
        sched_id = short_uuid()
        DBH.execute(
            "INSERT INTO schedules(id, chat_id, draft_id, run_at, created_by, status, created_at) VALUES(?,?,?,?,?,?,?)",
            (sched_id, chat.id, bound["id"], run_at, user.id, "scheduled", now_ts()),
        )
        context.job_queue.run_once(run_scheduled_exam_job, when=max(1, run_at - now_ts()), data={"schedule_id": sched_id}, name=f"schedule:{sched_id}")
        audit(user.id, "schedule_exam", sched_id, {"chat_id": chat.id, "draft_id": bound['id'], "run_at": run_at})
        await safe_reply(message, f"⏰ Scheduled: <code>{sched_id}</code> at {fmt_dt(run_at)}", parse_mode=ParseMode.HTML)
        return

    if command in {"listschedules", "schedules"}:
        rows = list_group_schedules(chat.id)
        if not rows:
            await safe_reply(message, "এই group এ কোনো scheduled exam নেই।")
            return
        lines = ["<b>Scheduled Exams</b>"]
        for row in rows:
            lines.append(f"• <code>{row['id']}</code> — {html_escape(row['title'])} — {fmt_dt(row['run_at'])}")
        await safe_reply(message, "\n".join(lines), parse_mode=ParseMode.HTML)
        return

    if command in {"cancelschedule", "unschedule"}:
        if not await is_group_admin_or_global(update, context):
            await safe_reply(message, "শুধু group admin / bot admin schedule cancel করতে পারবে।")
            return
        sched_id = args.strip().upper()
        if not sched_id:
            await safe_reply(message, "Usage: .cancelschedule SCHEDULE_ID")
            return
        DBH.execute("UPDATE schedules SET status='cancelled' WHERE id=? AND chat_id=?", (sched_id, chat.id))
        for job in context.job_queue.jobs():
            if job.name == f"schedule:{sched_id}":
                job.schedule_removal()
        audit(user.id, "cancel_schedule", sched_id, {"chat_id": chat.id})
        await safe_reply(message, f"❎ Cancelled schedule <code>{sched_id}</code>", parse_mode=ParseMode.HTML)
        return

async def handle_document_upload(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    message = update.effective_message
    user = update.effective_user
    chat = update.effective_chat
    if not message or not user or not chat or not message.document:
        return
    record_user(user)
    record_chat(chat)
    if chat.type != "private" or not is_bot_admin(user.id):
        return
    draft_id = get_active_draft_id(user.id)
    if not draft_id:
        await safe_reply(message, "আগে New Exam করে একটি active draft তৈরি করুন।")
        return
    filename = (message.document.file_name or "").lower()
    if not filename.endswith(".csv"):
        await safe_reply(message, "শুধু CSV file import করা যাবে।")
        return
    file = await message.document.get_file()
    content = await file.download_as_bytearray()
    added, errors = import_csv_questions(bytes(content), draft_id)
    draft = get_draft(draft_id)
    text = f"✅ CSV import complete. Added: <b>{added}</b>"
    if errors:
        text += f"\n⚠️ Errors: <b>{len(errors)}</b>\n" + "\n".join(html_escape(e) for e in errors[:10])
    await safe_reply(message, text, parse_mode=ParseMode.HTML)
    if draft:
        await send_draft_card(context, user.id, user.id, draft_id)
    audit(user.id, "import_csv", draft_id, {"added": added, "errors": len(errors)})


async def handle_poll_import(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    message = update.effective_message
    user = update.effective_user
    chat = update.effective_chat
    if not message or not user or not chat or not message.poll:
        return
    record_user(user)
    record_chat(chat)
    poll = message.poll
    if chat.type == "private" and is_bot_admin(user.id):
        draft_id = get_active_draft_id(user.id)
        if not draft_id:
            await safe_reply(message, "আগে New Exam করে active draft তৈরি করুন।")
            return
        if poll.type != Poll.QUIZ:
            await safe_reply(message, "শুধু quiz poll forward করলে import হবে।")
            return
        if poll.correct_option_id is None:
            await safe_reply(message, "এই forwarded quiz-এ Telegram correct answer দিচ্ছে না। CSV upload করুন বা quiz poll private chat এ আবার পাঠান।")
            return
        options = [opt.text for opt in poll.options]
        q_no = add_question_to_draft(
            draft_id,
            poll.question,
            options,
            int(poll.correct_option_id),
            poll.explanation or "",
            "forwarded_quiz",
        )
        await safe_reply(message, f"✅ Question added to <code>{draft_id}</code> as Q{q_no}", parse_mode=ParseMode.HTML)
        audit(user.id, "add_quiz_question", draft_id, {"q_no": q_no})


async def handle_poll_answer(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    answer = update.poll_answer
    if not answer:
        return
    user = answer.user
    record_user(user)
    poll_id = answer.poll_id
    qrow = get_question_by_poll(poll_id)
    if not qrow:
        return
    if qrow["session_status"] != "running":
        return
    if not answer.option_ids:
        return
    if not await is_required_channel_member(context, user.id):
        # ignore answers from non-members, but keep a participant record as ineligible for audit visibility
        DBH.execute(
            "INSERT INTO participants(session_id, user_id, username, display_name, eligible, last_answer_at) VALUES(?,?,?,?,0,?) ON CONFLICT(session_id,user_id) DO UPDATE SET eligible=0, last_answer_at=excluded.last_answer_at",
            (qrow["session_id"], user.id, user.username, choose_name(user.username, user.first_name, user.last_name, user.id), now_ts()),
        )
        return
    selected = int(answer.option_ids[0])
    is_correct_ans = 1 if selected == int(qrow["correct_option"]) else 0
    neg = float(qrow["negative_mark"])
    delta = 1.0 if is_correct_ans else (-neg)
    display_name = choose_name(user.username, user.first_name, user.last_name, user.id)
    with closing(DBH.connect()) as conn:
        old = conn.execute(
            "SELECT * FROM answers WHERE session_id=? AND q_no=? AND user_id=?",
            (qrow["session_id"], qrow["q_no"], user.id),
        ).fetchone()
        if old:
            # first answer only
            return
        conn.execute(
            "INSERT INTO answers(session_id, q_no, user_id, selected_option, is_correct, answered_at) VALUES(?,?,?,?,?,?)",
            (qrow["session_id"], qrow["q_no"], user.id, selected, is_correct_ans, now_ts()),
        )
        conn.execute(
            """
            INSERT INTO participants(session_id, user_id, username, display_name, eligible, correct_count, wrong_count, score, last_answer_at)
            VALUES(?,?,?,?,1,?,?,?,?)
            ON CONFLICT(session_id, user_id) DO UPDATE SET
                username=excluded.username,
                display_name=excluded.display_name,
                eligible=1,
                correct_count=participants.correct_count + excluded.correct_count,
                wrong_count=participants.wrong_count + excluded.wrong_count,
                score=participants.score + excluded.score,
                last_answer_at=excluded.last_answer_at
            """,
            (
                qrow["session_id"],
                user.id,
                user.username,
                display_name,
                1 if is_correct_ans else 0,
                0 if is_correct_ans else 1,
                delta,
                now_ts(),
            ),
        )
        conn.commit()


async def handle_restriction_and_bookkeeping(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    message = update.effective_message
    user = update.effective_user
    chat = update.effective_chat
    if not chat or not message or chat.type not in {"group", "supergroup"}:
        return
    if user:
        record_user(user)
    record_chat(chat)
    session = get_active_session(chat.id)
    if not session or session["status"] not in {"countdown", "running"}:
        return
    if not user or user.is_bot:
        return
    if await is_group_admin_or_global(update, context):
        return
    # during exam, delete all non-admin messages
    if message.text or message.caption or message.photo or message.document or message.sticker or message.video or message.voice or message.animation or message.audio:
        await safe_delete_message(context.bot, chat.id, message.message_id)


async def run_scheduled_exam_job(context: ContextTypes.DEFAULT_TYPE) -> None:
    sched_id = context.job.data["schedule_id"]
    sched = DBH.fetchone("SELECT * FROM schedules WHERE id=?", (sched_id,))
    if not sched or sched["status"] != "scheduled":
        return
    if get_active_session(int(sched["chat_id"])):
        DBH.execute("UPDATE schedules SET status='skipped' WHERE id=?", (sched_id,))
        return
    session_id = create_session_from_draft(str(sched["draft_id"]), int(sched["chat_id"]), int(sched["created_by"]))
    if not session_id:
        DBH.execute("UPDATE schedules SET status='failed' WHERE id=?", (sched_id,))
        return
    DBH.execute("UPDATE schedules SET status='done' WHERE id=?", (sched_id,))
    await start_exam_countdown(context, session_id)


async def restore_schedules(context: ContextTypes.DEFAULT_TYPE) -> None:
    rows = DBH.fetchall("SELECT * FROM schedules WHERE status='scheduled' ORDER BY run_at ASC")
    for row in rows:
        delay = int(row["run_at"]) - now_ts()
        if delay <= -300:
            DBH.execute("UPDATE schedules SET status='missed' WHERE id=?", (row["id"],))
            continue
        if delay < 0:
            delay = 1
        context.job_queue.run_once(run_scheduled_exam_job, when=delay, data={"schedule_id": row["id"]}, name=f"schedule:{row['id']}")


async def perform_broadcast(
    context: ContextTypes.DEFAULT_TYPE,
    owner_id: int,
    source_message: Optional[Message],
    text: Optional[str] = None,
    pin: bool = False,
) -> None:
    group_rows = DBH.fetchall("SELECT chat_id FROM known_chats WHERE active=1 AND chat_type IN ('group','supergroup')")
    user_rows = DBH.fetchall("SELECT user_id FROM known_users WHERE started=1")
    sent_groups = 0
    sent_users = 0
    for row in group_rows:
        try:
            if source_message:
                copied = await context.bot.copy_message(chat_id=row["chat_id"], from_chat_id=source_message.chat_id, message_id=source_message.message_id)
                if pin:
                    await safe_pin_message(context.bot, row["chat_id"], copied.message_id)
                    await delete_service_pin_later(context, int(row["chat_id"]))
            else:
                msg = await context.bot.send_message(row["chat_id"], text or "")
                if pin:
                    await safe_pin_message(context.bot, row["chat_id"], msg.message_id)
                    await delete_service_pin_later(context, int(row["chat_id"]))
            sent_groups += 1
        except TelegramError:
            continue
    for row in user_rows:
        try:
            if source_message:
                await context.bot.copy_message(chat_id=row["user_id"], from_chat_id=source_message.chat_id, message_id=source_message.message_id)
            else:
                await context.bot.send_message(row["user_id"], text or "")
            sent_users += 1
        except TelegramError:
            continue
    audit(owner_id, "broadcast", "all", {"groups": sent_groups, "users": sent_users, "pin": pin})


async def perform_announce(
    context: ContextTypes.DEFAULT_TYPE,
    owner_id: int,
    target_chat_id: int,
    source_message: Optional[Message],
    text: Optional[str] = None,
    pin: bool = False,
) -> None:
    if source_message:
        copied = await context.bot.copy_message(chat_id=target_chat_id, from_chat_id=source_message.chat_id, message_id=source_message.message_id)
        message_id = copied.message_id
    else:
        msg = await context.bot.send_message(chat_id=target_chat_id, text=text or "")
        message_id = msg.message_id
    if pin:
        await safe_pin_message(context.bot, target_chat_id, message_id)
        await delete_service_pin_later(context, target_chat_id)
    audit(owner_id, "announce", str(target_chat_id), {"pin": pin})


async def post_init(app: Application) -> None:
    me = await app.bot.get_me()
    app.bot_data["bot_username"] = me.username or ""
    await restore_schedules(app)
    app.job_queue.run_repeating(cleanup_old_data_job, interval=3600, first=300, name="cleanup")
    logger.info("Bot started as @%s", me.username)


async def error_handler(update: object, context: ContextTypes.DEFAULT_TYPE) -> None:
    err = context.error
    if err and "409 Conflict" in str(err):
        logger.warning("Another polling instance is using this bot token. Stop the duplicate instance.")
        return
    logger.exception("Unhandled error", exc_info=err)


# ============================================================
# Main
# ============================================================


def build_app() -> Application:
    app = (
        ApplicationBuilder()
        .token(CONFIG.bot_token)
        .post_init(post_init)
        .build()
    )

    app.add_handler(CallbackQueryHandler(callback_router), group=0)
    app.add_handler(PollAnswerHandler(handle_poll_answer), group=0)
    app.add_handler(ChatMemberHandler(handle_my_chat_member, chat_member_types=ChatMemberHandler.MY_CHAT_MEMBER), group=0)
    app.add_handler(MessageHandler(filters.StatusUpdate.PINNED_MESSAGE, handle_pinned_service), group=1)
    app.add_handler(MessageHandler(filters.Document.ALL, handle_document_upload), group=1)
    app.add_handler(MessageHandler(filters.POLL, handle_poll_import), group=1)
    app.add_handler(MessageHandler(filters.TEXT, handle_text), group=2)
    app.add_handler(MessageHandler(filters.ALL, handle_restriction_and_bookkeeping), group=10)
    app.add_error_handler(error_handler)
    return app



# ============================================================
# Final patch layer (special chars, themes, thumbnails, better PDF, private practice flow)
# ============================================================

import base64
import unicodedata
import urllib.error
import urllib.parse
import urllib.request
from telegram import (
    BotCommand,
    BotCommandScopeAllChatAdministrators,
    BotCommandScopeAllPrivateChats,
    BotCommandScopeChat,
)

THUMBS_DIR = DATA_DIR / "thumbs"
THUMBS_DIR.mkdir(parents=True, exist_ok=True)
GITHUB_TOKEN = os.getenv("GITHUB_TOKEN", "").strip()
GITHUB_REPO = os.getenv("GITHUB_REPO", "").strip()
GITHUB_BRANCH = os.getenv("GITHUB_BRANCH", "main").strip() or "main"
GITHUB_THUMB_DIR = os.getenv("GITHUB_THUMB_DIR", "assets/report-thumbs").strip().strip("/") or "assets/report-thumbs"

DBH.executescript(
    """
    CREATE TABLE IF NOT EXISTS user_visuals (
        user_id INTEGER PRIMARY KEY,
        theme_name TEXT DEFAULT 'midnight',
        custom_theme TEXT,
        thumb_path TEXT,
        thumb_preview_path TEXT,
        thumb_github_path TEXT,
        updated_at INTEGER NOT NULL DEFAULT 0
    );
    """
)

BUILTIN_THEMES: Dict[str, Dict[str, str]] = {
    "midnight": {
        "bg": "#03101F",
        "table": "#07162D",
        "card1": "#132744",
        "card2": "#0E2037",
        "text": "#EAF2FF",
        "muted": "#B9C7DD",
        "subtext": "#C8D8F4",
        "accent": "#D7F7CC",
        "footer": "#95A0B4",
        "outline": "#18324B",
    },
    "ocean": {
        "bg": "#071A24",
        "table": "#0A2A3A",
        "card1": "#114055",
        "card2": "#0C3447",
        "text": "#F1FBFF",
        "muted": "#B6D7E5",
        "subtext": "#CBE8F2",
        "accent": "#B8F3E0",
        "footer": "#8DAFBC",
        "outline": "#1D5368",
    },
    "emerald": {
        "bg": "#081712",
        "table": "#0E241C",
        "card1": "#17382B",
        "card2": "#112D22",
        "text": "#F4FFF9",
        "muted": "#BEDACB",
        "subtext": "#D3ECDD",
        "accent": "#DDF7C8",
        "footer": "#90A89A",
        "outline": "#2C5440",
    },
    "sunset": {
        "bg": "#1A0F13",
        "table": "#2A151D",
        "card1": "#4B2230",
        "card2": "#3E1D29",
        "text": "#FFF5F7",
        "muted": "#E3C8CD",
        "subtext": "#F0D4DA",
        "accent": "#F7EDBF",
        "footer": "#B39AA1",
        "outline": "#6A3445",
    },
}
THEME_KEYS = ["bg", "table", "card1", "card2", "text", "muted", "subtext", "accent", "footer", "outline"]

FONT_CANDIDATES.setdefault("symbols", [])
for _extra in [
    str(FONTS_DIR / "NotoSansSymbols2-Regular.ttf"),
    str(FONTS_DIR / "NotoEmoji-Regular.ttf"),
    str(FONTS_DIR / "NotoColorEmoji.ttf"),
    str(FONTS_DIR / "NotoSans-Regular.ttf"),
    "/usr/share/fonts/truetype/noto/NotoSansSymbols2-Regular.ttf",
    "/usr/share/fonts/truetype/noto/NotoEmoji-Regular.ttf",
    "/usr/share/fonts/truetype/noto/NotoColorEmoji.ttf",
    "/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf",
]:
    if _extra not in FONT_CANDIDATES["symbols"]:
        FONT_CANDIDATES["symbols"].append(_extra)
for _extra in [
    str(FONTS_DIR / "NotoEmoji-Regular.ttf"),
    str(FONTS_DIR / "NotoColorEmoji.ttf"),
    str(FONTS_DIR / "NotoSansSymbols2-Regular.ttf"),
]:
    if _extra not in FONT_CANDIDATES["emoji"]:
        FONT_CANDIDATES["emoji"].insert(0, _extra)
for _extra in [
    str(FONTS_DIR / "NotoSansSymbols2-Regular.ttf"),
    str(FONTS_DIR / "NotoSans-Regular.ttf"),
    str(FONTS_DIR / "NotoEmoji-Regular.ttf"),
]:
    if _extra not in FONT_CANDIDATES["regular"]:
        FONT_CANDIDATES["regular"].append(_extra)
    if _extra not in FONT_CANDIDATES["bold"]:
        FONT_CANDIDATES["bold"].append(_extra)



def normalize_visual_text(text: Any) -> str:
    value = str(text or "")
    value = unicodedata.normalize("NFKC", value)
    # map invisible fillers to normal spaces first
    for ch in ["\u3164", "\u115F", "\u1160", "\u2800"]:
        value = value.replace(ch, " ")
    # remove zero-width and control-ish formatting chars
    for ch in ["\u200B", "\u200C", "\u200D", "\u2060", "\uFEFF", "\u00AD"]:
        value = value.replace(ch, "")
    value = value.replace("\t", " ").replace("\r", "")
    value = re.sub(r"\s+", " ", value)
    return value.strip()


def _is_bengali(ch: str) -> bool:
    cp = ord(ch)
    return 0x0980 <= cp <= 0x09FF


def _is_emoji_or_symbol(ch: str) -> bool:
    cp = ord(ch)
    if 0x1F000 <= cp <= 0x1FAFF:
        return True
    if 0x2600 <= cp <= 0x27BF:
        return True
    return unicodedata.category(ch) in {"So", "Sk", "Sm"}


def _is_fancy_latin(ch: str) -> bool:
    cp = ord(ch)
    return (0x1D00 <= cp <= 0x1D7F) or (0x02B0 <= cp <= 0x02FF) or (0xA700 <= cp <= 0xA7FF)


def _is_visible_name_char(ch: str) -> bool:
    if not ch:
        return False
    cat = unicodedata.category(ch)
    if cat in {"Cf", "Cc", "Cs"}:
        return False
    return not ch.isspace()


def _name_visible_ratio(text: str) -> float:
    t = normalize_visual_text(text)
    if not t:
        return 0.0
    visible = sum(1 for ch in t if _is_visible_name_char(ch))
    return visible / max(1, len(t))


def _name_letter_digit_ratio(text: str) -> float:
    t = normalize_visual_text(text)
    if not t:
        return 0.0
    visible = 0
    letters_digits = 0
    for ch in t:
        if _is_visible_name_char(ch):
            visible += 1
            cat = unicodedata.category(ch)
            if cat.startswith("L") or cat.startswith("N"):
                letters_digits += 1
    if visible == 0:
        return 0.0
    return letters_digits / visible


def _extract_symbolic_name(text: str) -> str:
    t = normalize_visual_text(text)
    kept = []
    for ch in t:
        if _is_visible_name_char(ch) and (_is_emoji_or_symbol(ch) or unicodedata.category(ch).startswith("P")):
            kept.append(ch)
    out = "".join(kept).strip()
    return out[:24]


def _contains_problematic_name_chars(text: str) -> bool:
    t = normalize_visual_text(text)
    if not t:
        return True
    for ch in t:
        if not _is_visible_name_char(ch):
            continue
        cp = ord(ch)
        cat = unicodedata.category(ch)
        # Bengali is allowed.
        if _is_bengali(ch):
            continue
        # Basic printable ASCII and common punctuation are allowed.
        if 32 <= cp <= 126:
            continue
        # Plain emoji / symbols may be present, but if the whole name is mostly emoji we fallback later.
        if _is_emoji_or_symbol(ch):
            continue
        # Fancy latin/smallcaps almost always render unreliably -> treat as problematic.
        if _is_fancy_latin(ch):
            return True
        # Any other non-ASCII letter/mark tends to break in current fonts.
        if cat.startswith(("L", "M")):
            return True
    return False


def _is_probably_unreadable_name(text: str) -> bool:
    t = normalize_visual_text(text)
    if not t:
        return True
    if _name_visible_ratio(t) < 0.30:
        return True
    if _contains_problematic_name_chars(t):
        return True
    # Symbol-only or mostly-symbolic names are not useful as identity labels.
    visible = [ch for ch in t if _is_visible_name_char(ch)]
    if visible and all(_is_emoji_or_symbol(ch) or unicodedata.category(ch).startswith("P") for ch in visible):
        return True
    if _name_letter_digit_ratio(t) < 0.35 and not any(_is_bengali(ch) for ch in t):
        return True
    return False


def preferred_font_kind(text: str, bold: bool = False) -> str:
    text = normalize_visual_text(text)
    if not text:
        return "bold" if bold else "regular"
    # mixed Bengali/ASCII names render most reliably with regular/bold fonts;
    # usernames are shown separately as fallback.
    if any(_is_bengali(ch) for ch in text):
        return "bold" if bold else "regular"
    if any(_is_fancy_latin(ch) for ch in text):
        return "symbols"
    if any(_is_emoji_or_symbol(ch) for ch in text):
        return "emoji"
    return "bold" if bold else "regular"


def font_for_text(text: str, size: int, bold: bool = False):
    kind = preferred_font_kind(text, bold=bold)
    if kind == "emoji":
        return FONTS.get("emoji", size)
    if kind == "symbols":
        return FONTS.get("symbols", size) or FONTS.get("regular", size)
    return FONTS.get("bold" if bold else "regular", size)


def choose_name(username: Optional[str], first_name: Optional[str], last_name: Optional[str], user_id: Optional[int] = None) -> str:
    full = normalize_visual_text(" ".join(x for x in [first_name, last_name] if x))
    uname = normalize_visual_text(username or "")
    if uname and not uname.startswith("@"):
        uname = f"@{uname}"

    # Accept only clearly identifying visible names as primary display names.
    if full and (not _is_probably_unreadable_name(full)) and _label_has_identifying_chars(full):
        return full
    if uname:
        return uname
    return f"User {user_id}" if user_id else "Unknown User"


def split_user_labels(display_name: Optional[str], username: Optional[str], fallback_user_id: Optional[int] = None) -> Tuple[str, str]:
    raw_main = normalize_visual_text(display_name or "")
    uname = normalize_visual_text(username or "")
    if uname and not uname.startswith("@"):
        uname = f"@{uname}"

    primary = raw_main
    secondary = uname

    # If the display name is blank / invisible / symbol-only / unsupported,
    # always prefer a deterministic readable label.
    if not raw_main or _is_probably_unreadable_name(raw_main):
        if uname:
            primary = uname
            secondary = raw_main
        else:
            primary = f"User {fallback_user_id}" if fallback_user_id else "Unknown User"
            secondary = raw_main
    else:
        # Even if it is technically visible, fancy/problematic chars make it hard to identify.
        if _contains_problematic_name_chars(raw_main) and uname:
            primary = uname
            secondary = raw_main
        elif uname and uname == raw_main:
            secondary = ""

    primary = normalize_visual_text(primary) or (f"User {fallback_user_id}" if fallback_user_id else "Unknown User")
    secondary = normalize_visual_text(secondary or "")

    # If secondary is still unreadable, keep only a symbolic short trace if it exists.
    if secondary and _is_probably_unreadable_name(secondary):
        symbolic = _extract_symbolic_name(secondary)
        secondary = symbolic if symbolic and symbolic != primary else ""

    if secondary and secondary == primary:
        secondary = ""

    return primary[:80], secondary[:80]


def _label_has_identifying_chars(text: str) -> bool:
    t = normalize_visual_text(text)
    if not t:
        return False
    count = 0
    for ch in t:
        if _is_bengali(ch) or (ch.isascii() and (ch.isalpha() or ch.isdigit())):
            count += 1
            if count >= 2:
                return True
    return False


def finalize_render_labels(name: str, sub: str = "", user_id: Optional[int] = None) -> Tuple[str, str]:
    primary = normalize_visual_text(name)
    secondary = normalize_visual_text(sub)

    # If main line is not truly identifying, prefer @username on the main line.
    if not _label_has_identifying_chars(primary):
        if secondary.startswith("@") and _label_has_identifying_chars(secondary):
            original = primary
            primary = secondary
            secondary = original if original and original != primary else ""
        else:
            original = primary
            primary = f"User {user_id}" if user_id else "Unknown User"
            # keep a tiny symbolic trace only if available
            symbolic = _extract_symbolic_name(original)
            secondary = symbolic if symbolic and symbolic != primary else ""

    # If secondary is still useless, drop it.
    if secondary and not secondary.startswith("@") and not _label_has_identifying_chars(secondary):
        symbolic = _extract_symbolic_name(secondary)
        secondary = symbolic if symbolic and symbolic != primary else ""

    if secondary == primary:
        secondary = ""

    return primary[:80], secondary[:80]


def get_user_visual_row(user_id: int) -> Optional[sqlite3.Row]:
    return DBH.fetchone("SELECT * FROM user_visuals WHERE user_id=?", (user_id,))


def upsert_user_visual(user_id: int, **kwargs: Any) -> None:
    row = get_user_visual_row(user_id)
    base = {
        "theme_name": "midnight",
        "custom_theme": None,
        "thumb_path": None,
        "thumb_preview_path": None,
        "thumb_github_path": None,
    }
    if row:
        base.update({k: row[k] for k in base.keys()})
    base.update(kwargs)
    DBH.execute(
        """
        INSERT INTO user_visuals(user_id, theme_name, custom_theme, thumb_path, thumb_preview_path, thumb_github_path, updated_at)
        VALUES(?,?,?,?,?,?,?)
        ON CONFLICT(user_id) DO UPDATE SET
            theme_name=excluded.theme_name,
            custom_theme=excluded.custom_theme,
            thumb_path=excluded.thumb_path,
            thumb_preview_path=excluded.thumb_preview_path,
            thumb_github_path=excluded.thumb_github_path,
            updated_at=excluded.updated_at
        """,
        (
            user_id,
            base["theme_name"],
            base["custom_theme"],
            base["thumb_path"],
            base["thumb_preview_path"],
            base["thumb_github_path"],
            now_ts(),
        ),
    )


def parse_theme_custom_args(raw: str) -> Dict[str, str]:
    parts = [p.strip() for p in (raw or "").split() if p.strip()]
    out: Dict[str, str] = {}
    for part in parts:
        if "=" not in part:
            continue
        k, v = part.split("=", 1)
        k = k.strip().lower()
        v = v.strip()
        if k in THEME_KEYS and re.fullmatch(r"#[0-9A-Fa-f]{6}", v):
            out[k] = v.upper()
    return out


def get_user_theme(user_id: int) -> Tuple[str, Dict[str, str], Dict[str, str]]:
    row = get_user_visual_row(user_id)
    name = (row["theme_name"] if row and row["theme_name"] else "midnight").lower()
    if name not in BUILTIN_THEMES:
        name = "midnight"
    theme = dict(BUILTIN_THEMES[name])
    custom = jload(row["custom_theme"], {}) if row and row["custom_theme"] else {}
    if isinstance(custom, dict):
        for k, v in custom.items():
            if k in THEME_KEYS and isinstance(v, str) and re.fullmatch(r"#[0-9A-Fa-f]{6}", v):
                theme[k] = v.upper()
    else:
        custom = {}
    return name, theme, custom


def theme_text_summary(user_id: int) -> str:
    name, theme, custom = get_user_theme(user_id)
    lines = [
        f"Current theme: <b>{html_escape(name)}</b>",
        "",
        "Built-in themes: <code>midnight</code>, <code>ocean</code>, <code>emerald</code>, <code>sunset</code>",
        "",
        "Examples:",
        "<code>/theme ocean</code>",
        "<code>/theme sunset</code>",
        "<code>/theme custom bg=#03101F table=#07162D card1=#132744 card2=#0E2037 text=#EAF2FF muted=#B9C7DD subtext=#C8D8F4 accent=#D7F7CC footer=#95A0B4 outline=#18324B</code>",
        "",
        "Current colors:",
    ]
    for k in THEME_KEYS:
        lines.append(f"• <code>{k}</code> = <code>{html_escape(theme[k])}</code>")
    if custom:
        lines.append("")
        lines.append(f"Custom overrides: <code>{html_escape(jdump(custom))}</code>")
    return "\n".join(lines)


def _thumb_paths(user_id: int) -> Tuple[Path, Path]:
    return THUMBS_DIR / f"{user_id}_full.jpg", THUMBS_DIR / f"{user_id}_preview.jpg"


def _center_square(img: Image.Image) -> Image.Image:
    img = img.convert("RGB")
    w, h = img.size
    side = min(w, h)
    left = (w - side) // 2
    top = (h - side) // 2
    return img.crop((left, top, left + side, top + side))


def _save_jpeg_with_size_limit(img: Image.Image, path: Path, max_bytes: int = 190_000) -> None:
    quality = 88
    while quality >= 55:
        bio = io.BytesIO()
        img.save(bio, format="JPEG", quality=quality, optimize=True)
        data = bio.getvalue()
        if len(data) <= max_bytes or quality <= 60:
            path.write_bytes(data)
            return
        quality -= 7
    path.write_bytes(data)


def _github_request(method: str, url: str, payload: Optional[dict] = None) -> Any:
    headers = {
        "Accept": "application/vnd.github+json",
        "X-GitHub-Api-Version": "2022-11-28",
        "Authorization": f"Bearer {GITHUB_TOKEN}",
        "User-Agent": f"{CONFIG.brand_name} thumbnail-sync",
    }
    data = None
    if payload is not None:
        data = json.dumps(payload).encode("utf-8")
        headers["Content-Type"] = "application/json"
    req = urllib.request.Request(url, data=data, method=method, headers=headers)
    with urllib.request.urlopen(req, timeout=25) as resp:
        raw = resp.read().decode("utf-8")
    return json.loads(raw) if raw else None


def sync_thumbnail_to_github(user_id: int, preview_bytes: bytes) -> Optional[str]:
    if not (GITHUB_TOKEN and GITHUB_REPO):
        return None
    path = f"{GITHUB_THUMB_DIR}/{user_id}.jpg"
    encoded_path = urllib.parse.quote(path, safe="")
    url = f"https://api.github.com/repos/{GITHUB_REPO}/contents/{encoded_path}"
    sha = None
    try:
        existing = _github_request("GET", f"{url}?ref={urllib.parse.quote(GITHUB_BRANCH, safe='')}")
        sha = existing.get("sha") if isinstance(existing, dict) else None
    except Exception:
        sha = None
    payload = {
        "message": f"Update report thumbnail for {user_id}",
        "content": base64.b64encode(preview_bytes).decode("ascii"),
        "branch": GITHUB_BRANCH,
    }
    if sha:
        payload["sha"] = sha
    try:
        _github_request("PUT", url, payload)
        return path
    except Exception as exc:
        logger.warning("GitHub thumbnail sync failed for %s: %s", user_id, exc)
        return None


def save_report_thumbnail(user_id: int, image_bytes: bytes) -> Tuple[Path, Path, Optional[str]]:
    img = Image.open(io.BytesIO(image_bytes))
    img = _center_square(img)
    full = img.resize((640, 640), Image.LANCZOS)
    preview = img.resize((320, 320), Image.LANCZOS)
    full_path, preview_path = _thumb_paths(user_id)
    full.save(full_path, format="JPEG", quality=90, optimize=True)
    _save_jpeg_with_size_limit(preview, preview_path)
    github_path = None
    try:
        github_path = sync_thumbnail_to_github(user_id, preview_path.read_bytes())
    except Exception as exc:
        logger.warning("Thumbnail sync skipped for %s: %s", user_id, exc)
    upsert_user_visual(user_id, thumb_path=str(full_path), thumb_preview_path=str(preview_path), thumb_github_path=github_path)
    return full_path, preview_path, github_path


def clear_report_thumbnail(user_id: int) -> None:
    full_path, preview_path = _thumb_paths(user_id)
    with suppress(Exception):
        if full_path.exists():
            full_path.unlink()
    with suppress(Exception):
        if preview_path.exists():
            preview_path.unlink()
    upsert_user_visual(user_id, thumb_path=None, thumb_preview_path=None, thumb_github_path=None)


def default_report_thumbnail_bytes(title: str, user_id: int) -> bytes:
    _, theme, _ = get_user_theme(user_id)
    img = Image.new("RGB", (320, 320), theme["bg"])
    dr = ImageDraw.Draw(img)
    dr.rounded_rectangle((18, 18, 302, 302), radius=28, fill=theme["table"], outline=theme["outline"], width=2)
    badge_font = font_for_text("Report", 26, bold=True)
    title_font = font_for_text(title, 34, bold=True)
    sub_font = font_for_text(CONFIG.brand_name, 18, bold=False)
    dr.text((34, 34), "EXAM REPORT", font=badge_font, fill=theme["accent"])
    _, bottom = draw_multiline(dr, normalize_visual_text(title or "Exam"), (34, 86), title_font, theme["text"], 252, line_gap=4)
    dr.text((34, bottom + 12), CONFIG.brand_name, font=sub_font, fill=theme["muted"])
    bio = io.BytesIO()
    img.save(bio, format="JPEG", quality=82, optimize=True)
    return bio.getvalue()


def get_report_thumbnail_bytes(user_id: int, title: str) -> bytes:
    row = get_user_visual_row(user_id)
    if row and row["thumb_preview_path"]:
        p = Path(str(row["thumb_preview_path"]))
        if p.exists():
            return p.read_bytes()
    return default_report_thumbnail_bytes(title, user_id)


def build_commands_text(chat_type: str, is_admin_user: bool, is_owner_user: bool) -> str:
    lines: List[str] = ["<b>Command List</b>", "সব command <b>/</b> এবং <b>.</b> — দুই prefix এই কাজ করবে।", ""]
    if chat_type == "private":
        lines.extend([
            "<b>Everyone</b>",
            "• /start — bot activate / result DM enable",
            "• /start practice_TOKEN — practice exam start (generated link)",
            "• /stoptqex — চলমান practice/exam stop করে partial result দেখুন",
            "• /help or /commands — command list",
        ])
        if is_admin_user:
            lines.extend([
                "",
                "<b>Admin / Owner (PM)</b>",
                "• /panel — button panel",
                "• /newexam — new exam draft create",
                "• /drafts or /mydrafts — my drafts list",
                "• /csvformat — CSV column format",
                "• /setthumb — report thumbnail photo set",
                "• /clearthumb — custom thumbnail remove",
                "• /thumbstatus — thumbnail status দেখুন",
                "• /cancel — current input flow cancel",
            ])
        if is_owner_user:
            lines.extend([
                "",
                "<b>Owner Only (PM)</b>",
                "• /theme — current theme and help",
                "• /theme midnight|ocean|emerald|sunset — built-in theme",
                "• /theme custom key=#HEX ... — custom colors",
                "• /addadmin [user_id] — add bot admin",
                "• /rmadmin [user_id] — remove bot admin",
                "• /admins — admin list",
                "• /audit — recent admin actions",
                "• /logs — memory, uptime, recent errors + full log",
                "• /broadcast [pin] — all groups + started users",
                "• /announce CHAT_ID [pin] — one target chat",
                "• /restart — restart bot process",
            ])
    else:
        lines.extend([
            "<b>Group Admin / Bot Admin</b>",
            "• /binddraft CODE — bind draft manually",
            "• /examstatus — current binding/exam status",
            "• /starttqex [DRAFTCODE] — ready button / start selected exam",
            "• /stoptqex — stop running exam",
            "• /schedule YYYY-MM-DD HH:MM — schedule exam",
            "• /listschedules — list scheduled exams",
            "• /cancelschedule SCHEDULE_ID — cancel schedule",
        ])
    return "\n".join(lines)


async def ensure_fonts_hint_file() -> str:
    return (
        "fonts/ folder এ ideally এই file গুলো রাখুন: "
        "NotoSansBengali-Regular.ttf, NotoSansBengali-Bold.ttf, NotoSans-Regular.ttf, NotoSans-Bold.ttf, "
        "NotoSansSymbols2-Regular.ttf, NotoEmoji-Regular.ttf"
    )


def render_leaderboard_png(title: str, items: List[Dict[str, Any]], theme: Optional[Dict[str, str]] = None) -> bytes:
    theme = dict(theme or BUILTIN_THEMES["midnight"])
    width = 1600
    title = normalize_visual_text(title) or "Exam"
    working = items or [{"name": "No eligible participants", "sub": "", "score": "0.00"}]
    probe = ImageDraw.Draw(Image.new("RGB", (10, 10)))
    title_font = font_for_text(f"LEADERBOARD — {title}", 68, bold=True)
    title_lines = wrap_text(probe, f"LEADERBOARD — {title}", title_font, width - 120)
    height = 300 + len(title_lines) * 84 + max(1, len(working)) * 118 + 110
    img = Image.new("RGB", (width, height), theme["bg"])
    draw = ImageDraw.Draw(img)

    sub_font = font_for_text("sub", 33, bold=False)
    head_font = font_for_text("HEAD", 42, bold=True)
    score_font = font_for_text("88.88", 48, bold=True)
    small_font = font_for_text("small", 24, bold=False)

    _, title_bottom = draw_multiline(draw, f"LEADERBOARD — {title}", (60, 36), title_font, theme["text"], width - 120, line_gap=8)
    draw.text((60, title_bottom + 2), "Top performers (score includes negative marking)", font=sub_font, fill=theme["muted"])

    table_x = 50
    table_y = title_bottom + 70
    table_w = width - 100
    draw.rounded_rectangle((table_x, table_y, table_x + table_w, table_y + 88), radius=24, fill=theme["table"])
    draw.text((table_x + 32, table_y + 22), "Rank", font=head_font, fill="#F5F7FF")
    draw.text((table_x + 190, table_y + 22), "Name", font=head_font, fill="#F5F7FF")
    draw.text((table_x + table_w - 220, table_y + 22), "Score", font=head_font, fill="#F5F7FF")

    y = table_y + 112
    for idx, item in enumerate(working, start=1):
        fill = theme["card1"] if idx == 1 else theme["card2"]
        draw.rounded_rectangle((table_x, y, table_x + table_w, y + 96), radius=24, fill=fill)
        draw.text((table_x + 34, y + 21), str(idx), font=head_font, fill="#F8FBFF")
        name, sub = finalize_render_labels(
            item.get("name") or "Unknown",
            item.get("sub") or "",
            int(item.get("user_id") or 0) or None,
        )
        score = str(item.get("score") or "0.00")
        max_name_w = table_w - 540
        name_font = font_for_text(name, 39, bold=False)
        sub_font_row = font_for_text(sub or name, 24, bold=False)
        name_lines = wrap_text(draw, name, name_font, max_name_w)
        primary_line = name_lines[0] if name_lines else name or "Unknown User"
        draw.text((table_x + 185, y + 15), primary_line, font=name_font, fill="#EDF4FF")
        if sub:
            sub_show = sub if len(sub) <= 28 else sub[:27] + "…"
            draw.text((table_x + 188, y + 56), sub_show, font=sub_font_row, fill=theme["subtext"])
        elif len(name_lines) > 1:
            draw.text((table_x + 188, y + 56), name_lines[1], font=sub_font_row, fill=theme["subtext"])
        sb = draw.textbbox((0, 0), score, font=score_font)
        draw.text((table_x + table_w - 70 - (sb[2] - sb[0]), y + 19), score, font=score_font, fill=theme["accent"])
        y += 116

    draw.text((60, height - 52), f"Generated by {CONFIG.brand_name}", font=small_font, fill=theme["footer"])
    buf = io.BytesIO()
    img.save(buf, format="PNG", optimize=True)
    return buf.getvalue()


def render_report_pdf(title: str, summary: Dict[str, Any], ranking: List[Dict[str, Any]], theme: Optional[Dict[str, str]] = None) -> bytes:
    theme = dict(theme or BUILTIN_THEMES["midnight"])
    pages: List[Image.Image] = []
    width, height = 1654, 2339
    title = normalize_visual_text(title) or "Exam"
    header_font = font_for_text(CONFIG.brand_name, 30, bold=True)
    title_font = font_for_text(title, 52, bold=True)
    section_font = font_for_text("Section", 30, bold=True)
    body_font = font_for_text("Body", 24, bold=False)
    small_font = font_for_text("Small", 20, bold=False)

    def new_page(page_no: int, total_pages: int) -> Tuple[Image.Image, ImageDraw.ImageDraw, int]:
        page = Image.new("RGB", (width, height), "#FFFFFF")
        dr = ImageDraw.Draw(page)
        dr.rounded_rectangle((40, 40, width - 40, height - 40), radius=26, outline="#D8E2EF", width=3)
        dr.text((72, 70), f"{CONFIG.brand_name} • Exam Report", font=header_font, fill="#18324B")
        _, bottom = draw_multiline(dr, title or "Exam", (72, 118), title_font, "#101820", width - 144, line_gap=6)
        dr.text((72, bottom + 4), f"Generated at {fmt_dt(now_ts())}", font=small_font, fill="#6B7A8B")
        dr.text((width - 210, 74), f"Page {page_no}/{total_pages}", font=small_font, fill="#6B7A8B")
        return page, dr, bottom + 46

    def draw_key_values(dr, y, items):
        left = 72
        box_w = (width - 144 - 18) // 2
        row_h = 76
        for idx, (k, v) in enumerate(items):
            col = idx % 2
            row = idx // 2
            x1 = left + col * (box_w + 18)
            y1 = y + row * (row_h + 16)
            dr.rounded_rectangle((x1, y1, x1 + box_w, y1 + row_h), radius=18, fill="#F6FAFD", outline="#DCE8F2")
            dr.text((x1 + 24, y1 + 14), str(k), font=small_font, fill="#587086")
            v_font = font_for_text(str(v), 34, bold=True)
            dr.text((x1 + 24, y1 + 38), str(v), font=v_font, fill="#0F2235")
        rows = (len(items) + 1) // 2
        return y + rows * (row_h + 16)

    rows_per_page = 34
    all_rows = ranking or [{"rank": 1, "name": "No eligible participants", "sub_name": "", "correct": 0, "wrong": 0, "skipped": int(summary["questions"]), "score": "0.00"}]
    chunks = list(chunked(all_rows, rows_per_page)) or [[]]
    total_pages = len(chunks)
    for page_no, chunk in enumerate(chunks, start=1):
        page, dr, y = new_page(page_no, total_pages)
        if page_no == 1:
            y = draw_key_values(dr, y, [
                ("Participants", summary["participants"]),
                ("Questions", summary["questions"]),
                ("Average Score", summary["average_score"]),
                ("Highest Score", summary["highest_score"]),
                ("Lowest Score", summary["lowest_score"]),
                ("Negative / Wrong", summary["negative_mark"]),
                ("Started", summary["started_at"]),
                ("Ended", summary["ended_at"]),
            ])
            y += 16
        dr.text((72, y), "Ranking Analysis", font=section_font, fill="#18324B")
        y += 44
        dr.rounded_rectangle((72, y, width - 72, y + 48), radius=14, fill=theme["table"])
        cols = [(92, "#"), (150, "Name"), (940, "Correct"), (1100, "Wrong"), (1255, "Skipped"), (1405, "Score")]
        for x, label in cols:
            dr.text((x, y + 12), label, font=small_font, fill="#FFFFFF")
        y += 60
        row_h = 50
        for item in chunk:
            dr.rounded_rectangle((72, y, width - 72, y + row_h), radius=12, fill="#F8FBFE", outline="#DFE8F1")
            primary, sub = finalize_render_labels(
                item.get("name", ""),
                item.get("sub_name", ""),
                int(item.get("user_id") or 0) or None,
            )
            if not primary:
                primary = "Unknown User"
            dr.text((92, y + 12), str(item["rank"]), font=body_font, fill="#102030")
            p_font = font_for_text(primary, 24, bold=False)
            dr.text((150, y + 8), primary[:34] + ("…" if len(primary) > 34 else ""), font=p_font, fill="#102030")
            if sub:
                s_font = font_for_text(sub, 20, bold=False)
                dr.text((150, y + 28), sub[:28] + ("…" if len(sub) > 28 else ""), font=s_font, fill="#627B90")
            dr.text((940, y + 12), str(item["correct"]), font=body_font, fill="#1C7C38")
            dr.text((1100, y + 12), str(item["wrong"]), font=body_font, fill="#B94040")
            dr.text((1255, y + 12), str(item["skipped"]), font=body_font, fill="#A77412")
            dr.text((1405, y + 12), str(item["score"]), font=body_font, fill="#102030")
            y += row_h + 10
        pages.append(page)
    rgb_pages = [p.convert("RGB") for p in pages]
    buf = io.BytesIO()
    rgb_pages[0].save(buf, format="PDF", save_all=True, append_images=rgb_pages[1:], resolution=150.0)
    return buf.getvalue()


_original_start_practice_from_token = start_practice_from_token
async def start_practice_from_token(update: Update, context: ContextTypes.DEFAULT_TYPE, token: str) -> None:
    message = update.effective_message
    user = update.effective_user
    if not message or not user:
        return
    record_user(user)
    mark_started(user)
    joined = await is_required_channel_member(context, user.id)
    if not joined:
        kb = InlineKeyboardMarkup([[InlineKeyboardButton("Join Required Channel", url=f"https://t.me/{CONFIG.required_channel.lstrip('@')}")]])
        await safe_reply(message, f"এই bot ব্যবহার করতে আগে {CONFIG.required_channel} channel এ join করুন। তারপর আবার practice link open করুন।", reply_markup=kb)
        return
    row = get_practice_link_by_token(token)
    if not row:
        await safe_reply(message, "এই practice link invalid বা disabled।")
        return
    q_count_row = DBH.fetchone("SELECT COUNT(*) AS c FROM draft_questions WHERE draft_id=?", (row["draft_id"],))
    q_count = int(q_count_row["c"] if q_count_row else 0)
    if q_count <= 0:
        await safe_reply(message, "এই practice exam এ এখনও কোনো প্রশ্ন নেই।")
        return
    attempts = get_practice_attempts(row["draft_id"], user.id)
    max_attempts = int(row["max_attempts"])
    if attempts >= max_attempts:
        await safe_reply(message, f"আপনি এই practice exam সর্বোচ্চ {max_attempts} বার দিয়েছেন।")
        return
    if get_active_session(user.id):
        await safe_reply(message, "আপনার inbox এ ইতিমধ্যে একটি চলমান exam/practice আছে। শেষ হলে আবার চেষ্টা করুন।")
        return
    new_attempt = register_practice_attempt(row["draft_id"], user.id)
    session_id = create_session_from_draft(row["draft_id"], user.id, user.id)
    if not session_id:
        await safe_reply(message, "Practice session create করা যায়নি।")
        return
    sent = await safe_reply(
        message,
        f"<b>Practice Ready</b>\n"
        f"<b>{html_escape(normalize_visual_text(row['title']))}</b>\n"
        f"Questions: <b>{q_count}</b>\n"
        f"Time / question: <b>{row['question_time']} sec</b>\n"
        f"Negative / wrong: <b>{row['negative_mark']}</b>\n"
        f"Attempt: <b>{new_attempt}/{max_attempts}</b>",
        parse_mode=ParseMode.HTML,
    )
    await start_exam_countdown(context, session_id, existing_message_id=sent.message_id if sent else None)


async def send_private_results(context: ContextTypes.DEFAULT_TYPE, session_id: str) -> None:
    session = get_session(session_id)
    if not session:
        return
    chat_row = DBH.fetchone("SELECT username, chat_type FROM known_chats WHERE chat_id=?", (session["chat_id"],))
    username = chat_row["username"] if chat_row else None
    is_private_exam = ((chat_row["chat_type"] if chat_row else "") or "") == "private"
    ranking = get_session_ranking(session_id)
    rank_map = {r["user_id"]: r for r in ranking}
    qrows = DBH.fetchall("SELECT q_no, message_id, question FROM session_questions WHERE session_id=? ORDER BY q_no", (session_id,))
    q_map = {int(r["q_no"]): r for r in qrows}
    participants = DBH.fetchall("SELECT * FROM participants WHERE session_id=? AND eligible=1", (session_id,))
    for p in participants:
        row = DBH.fetchone("SELECT started FROM known_users WHERE user_id=?", (p["user_id"],))
        if not row or int(row["started"]) != 1:
            continue
        rank_item = rank_map.get(int(p["user_id"]))
        if not rank_item:
            continue
        if not await is_required_channel_member(context, int(p["user_id"])):
            continue
        answers = DBH.fetchall("SELECT * FROM answers WHERE session_id=? AND user_id=? ORDER BY q_no", (session_id, p["user_id"]))
        answer_by_q = {int(a["q_no"]): a for a in answers}
        correct_links: List[str] = []
        wrong_links: List[str] = []
        skipped_links: List[str] = []
        for q_no, q in q_map.items():
            link = get_message_link(int(session["chat_id"]), int(q["message_id"] or 0), username)
            anchor = f"Q{q_no}"
            label = f"<a href=\"{link}\">{anchor}</a>" if link else anchor
            ans = answer_by_q.get(q_no)
            if ans is None:
                skipped_links.append(label)
            elif int(ans["is_correct"]) == 1:
                correct_links.append(label)
            else:
                wrong_links.append(label)
        display_primary, _display_sub = finalize_render_labels(rank_item.get("name", ""), rank_item.get("sub_name", ""), int(p["user_id"]))
        rank_line = "" if is_private_exam else f"Your rank: <b>#{rank_item['rank']}</b>\n"
        text = (
            f"<b>{html_escape(normalize_visual_text(session['title']))}</b>\n"
            f"{rank_line}"
            f"✅ Correct: <b>{rank_item['correct']}</b>\n"
            f"❌ Wrong: <b>{rank_item['wrong']}</b>\n"
            f"➖ Skipped: <b>{rank_item['skipped']}</b>\n"
            f"🏁 Final Score: <b>{rank_item['score']}</b>\n\n"
            f"<b>Correct Links</b>\n{', '.join(correct_links) or '—'}\n\n"
            f"<b>Wrong Links</b>\n{', '.join(wrong_links) or '—'}\n\n"
            f"<b>Skipped Links</b>\n{', '.join(skipped_links) or '—'}"
        )
        with suppress(TelegramError):
            await context.bot.send_message(
                chat_id=p["user_id"],
                text=text,
                parse_mode=ParseMode.HTML,
                link_preview_options=LinkPreviewOptions(is_disabled=True),
            )


async def send_admin_pdf_report(context: ContextTypes.DEFAULT_TYPE, session_id: str, ranking: List[Dict[str, Any]]) -> None:
    session = get_session(session_id)
    if not session:
        return
    rows = DBH.fetchall("SELECT score FROM participants WHERE session_id=? AND eligible=1", (session_id,))
    scores = [float(r["score"]) for r in rows] or [0.0]
    creator_id = int(session["created_by"])
    _, theme, _ = get_user_theme(creator_id)
    summary = {
        "participants": len(ranking),
        "questions": int(session["total_questions"]),
        "average_score": fmt_score(sum(scores) / len(scores)),
        "highest_score": fmt_score(max(scores)),
        "lowest_score": fmt_score(min(scores)),
        "negative_mark": session["negative_mark"],
        "started_at": fmt_dt(session["started_at"]),
        "ended_at": fmt_dt(session["ended_at"]),
    }
    pdf_bytes = render_report_pdf(session["title"], summary, ranking, theme=theme)
    thumb_bytes = get_report_thumbnail_bytes(creator_id, session["title"])
    recipients: List[int] = []
    for uid in [creator_id] + list(CONFIG.owner_ids) + all_admin_ids():
        if uid not in recipients:
            recipients.append(uid)
    logger.info("Sending PDF report for %s to recipients=%s", session_id, recipients)
    sent_any = False
    for uid in recipients:
        try:
            await context.bot.send_document(
                uid,
                document=InputFile(io.BytesIO(pdf_bytes), filename=f"{pdf_safe_filename(session['title'])}_report.pdf"),
                thumbnail=InputFile(io.BytesIO(thumb_bytes), filename="report_preview.jpg"),
                caption=f"📄 {normalize_visual_text(session['title'])} analysis report",
            )
            sent_any = True
        except TelegramError as exc:
            logger.warning("Could not send PDF report to %s: %s", uid, exc)
    if not sent_any:
        logger.warning("PDF report for %s was not delivered to any recipient", session_id)


async def finish_exam(context: ContextTypes.DEFAULT_TYPE, session_id: str, reason: str = "completed") -> None:
    session = get_session(session_id)
    if not session or session["status"] in {"finished", "stopped"}:
        return
    chat_id = int(session["chat_id"])
    chat_row = DBH.fetchone("SELECT chat_type FROM known_chats WHERE chat_id=?", (chat_id,))
    chat_type = (chat_row["chat_type"] if chat_row else "") or ""
    is_private_exam = chat_type == "private"

    for prefix in (f"close:{session_id}:", f"advance:{session_id}"):
        for job in context.job_queue.jobs():
            if job.name and job.name.startswith(prefix):
                job.schedule_removal()

    DBH.execute(
        "UPDATE sessions SET status=?, ended_at=?, active_poll_id=NULL, active_poll_message_id=NULL WHERE id=?",
        ("finished" if reason == "completed" else "stopped", now_ts(), session_id),
    )
    ranking = get_session_ranking(session_id)
    top = ranking[: CONFIG.scoreboard_top_n]
    leaderboard_rows = [{"name": item["name"], "sub": item.get("sub_name", ""), "score": item["score"]} for item in top]
    _, theme, _ = get_user_theme(int(session["created_by"]))
    image_bytes = render_leaderboard_png(session["title"], leaderboard_rows or [{"name": "No eligible participants", "sub": "", "score": "0.00"}], theme=theme)

    try:
        await context.bot.send_chat_action(chat_id=chat_id, action=ChatAction.UPLOAD_PHOTO)
        await context.bot.send_photo(chat_id=chat_id, photo=InputFile(io.BytesIO(image_bytes), filename="leaderboard.png"), caption=f"🏁 {normalize_visual_text(session['title'])} finished.")
    except TelegramError as exc:
        logger.warning("Could not send leaderboard image for %s: %s", session_id, exc)

    try:
        await send_private_results(context, session_id)
    except Exception:
        logger.exception("Failed to send private results for %s", session_id)

    if not is_private_exam:
        try:
            await send_admin_pdf_report(context, session_id, ranking)
        except Exception:
            logger.exception("Failed to send admin PDF report for %s", session_id)

    if not is_private_exam:
        DBH.execute("DELETE FROM group_bindings WHERE chat_id=?", (chat_id,))
        draft = get_draft(session["draft_id"])
        if draft:
            delete_draft(draft["id"], int(session["created_by"]))

    retention_ts = now_ts() + (CONFIG.retention_hours * 3600)
    queue_delete("session", session_id, retention_ts)
    audit(int(session["created_by"]), "finish_exam", session_id, {"reason": reason, "participants": len(ranking)})


async def handle_poll_answer(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    answer = update.poll_answer
    if not answer:
        return
    user = answer.user
    record_user(user)
    poll_id = answer.poll_id
    qrow = get_question_by_poll(poll_id)
    if not qrow:
        return
    if qrow["session_status"] != "running":
        return
    if not answer.option_ids:
        return
    if not await is_required_channel_member(context, user.id):
        DBH.execute(
            "INSERT INTO participants(session_id, user_id, username, display_name, eligible, last_answer_at) VALUES(?,?,?,?,0,?) ON CONFLICT(session_id,user_id) DO UPDATE SET eligible=0, last_answer_at=excluded.last_answer_at",
            (qrow["session_id"], user.id, user.username, choose_name(user.username, user.first_name, user.last_name, user.id), now_ts()),
        )
        return
    selected = int(answer.option_ids[0])
    is_correct_ans = 1 if selected == int(qrow["correct_option"]) else 0
    neg = float(qrow["negative_mark"])
    delta = 1.0 if is_correct_ans else (-neg)
    display_name = choose_name(user.username, user.first_name, user.last_name, user.id)
    with closing(DBH.connect()) as conn:
        old = conn.execute(
            "SELECT * FROM answers WHERE session_id=? AND q_no=? AND user_id=?",
            (qrow["session_id"], qrow["q_no"], user.id),
        ).fetchone()
        if old:
            return
        conn.execute(
            "INSERT INTO answers(session_id, q_no, user_id, selected_option, is_correct, answered_at) VALUES(?,?,?,?,?,?)",
            (qrow["session_id"], qrow["q_no"], user.id, selected, is_correct_ans, now_ts()),
        )
        conn.execute(
            """
            INSERT INTO participants(session_id, user_id, username, display_name, eligible, correct_count, wrong_count, score, last_answer_at)
            VALUES(?,?,?,?,1,?,?,?,?)
            ON CONFLICT(session_id, user_id) DO UPDATE SET
                username=excluded.username,
                display_name=excluded.display_name,
                eligible=1,
                correct_count=participants.correct_count + excluded.correct_count,
                wrong_count=participants.wrong_count + excluded.wrong_count,
                score=participants.score + excluded.score,
                last_answer_at=excluded.last_answer_at
            """,
            (
                qrow["session_id"],
                user.id,
                user.username,
                display_name,
                1 if is_correct_ans else 0,
                0 if is_correct_ans else 1,
                delta,
                now_ts(),
            ),
        )
        conn.commit()

    session = get_session(qrow["session_id"])
    if not session:
        return
    chat_row = DBH.fetchone("SELECT chat_type FROM known_chats WHERE chat_id=?", (session["chat_id"],))
    if ((chat_row["chat_type"] if chat_row else "") or "") == "private":
        close_job_name = f"close:{qrow['session_id']}:{qrow['q_no']}"
        for job in context.job_queue.get_jobs_by_name(close_job_name):
            job.schedule_removal()
        with suppress(TelegramError):
            await context.bot.stop_poll(chat_id=session["chat_id"], message_id=int(qrow["message_id"] or 0))
        set_session_active_poll(qrow["session_id"], None, None)
        context.job_queue.run_once(begin_or_advance_exam_job, when=0.2, data={"session_id": qrow["session_id"]}, name=f"advance:{qrow['session_id']}:private:{qrow['q_no']}")


async def handle_photo_upload(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    message = update.effective_message
    user = update.effective_user
    chat = update.effective_chat
    if not message or not user or not chat or not message.photo:
        return
    if chat.type != "private" or not user_has_staff_access(user.id):
        return
    state, payload = get_user_state(user.id)
    if state != "await_thumbnail_photo":
        return
    photo = message.photo[-1]
    file = await photo.get_file()
    data = bytes(await file.download_as_bytearray())
    full_path, preview_path, github_path = await asyncio.to_thread(save_report_thumbnail, user.id, data)
    clear_user_state(user.id)
    text = (
        "✅ Report thumbnail saved.\n"
        f"Local preview: <code>{html_escape(str(preview_path.relative_to(BASE_DIR) if preview_path.is_absolute() else preview_path))}</code>"
    )
    if github_path:
        text += f"\nGitHub path: <code>{html_escape(github_path)}</code>"
    elif GITHUB_REPO:
        text += "\nGitHub sync failed বা disabled. Local file ব্যবহার হবে।"
    await safe_reply(message, text, parse_mode=ParseMode.HTML)


_original_handle_document_upload = handle_document_upload
async def handle_document_upload(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    message = update.effective_message
    user = update.effective_user
    chat = update.effective_chat
    if message and user and chat and chat.type == "private" and user_has_staff_access(user.id):
        state, _payload = get_user_state(user.id)
        if state == "await_thumbnail_photo" and message.document and (message.document.mime_type or "").startswith("image/"):
            file = await message.document.get_file()
            data = bytes(await file.download_as_bytearray())
            full_path, preview_path, github_path = await asyncio.to_thread(save_report_thumbnail, user.id, data)
            clear_user_state(user.id)
            text = (
                "✅ Report thumbnail saved from image document.\n"
                f"Local preview: <code>{html_escape(str(preview_path.relative_to(BASE_DIR) if preview_path.is_absolute() else preview_path))}</code>"
            )
            if github_path:
                text += f"\nGitHub path: <code>{html_escape(github_path)}</code>"
            await safe_reply(message, text, parse_mode=ParseMode.HTML)
            return
    await _original_handle_document_upload(update, context)


_original_handle_text = handle_text
async def handle_text(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    message = update.effective_message
    user = update.effective_user
    chat = update.effective_chat
    if not message or not user or not chat or not message.text:
        return
    command, args = extract_command(message.text, context.bot_data.get("bot_username", ""))
    cmd = (command or "").lower()

    if chat.type == "private" and cmd == "stoptqex":
        session = get_active_session(user.id)
        if not session:
            await safe_reply(message, "আপনার inbox এ কোনো active practice/exam নেই।")
            return
        await finish_exam(context, session["id"], reason="manual_stop")
        await safe_reply(message, "🛑 Practice/Exam stopped. যতটুকু দিয়েছেন ততটুকুর result পাঠানো হয়েছে।")
        return

    if chat.type == "private" and cmd == "theme":
        if not is_owner(user.id):
            await safe_reply(message, "Only owner theme change করতে পারবে।")
            return
        raw = (args or "").strip()
        if not raw or raw.lower() in {"show", "current", "list"}:
            await safe_reply(message, theme_text_summary(user.id), parse_mode=ParseMode.HTML, disable_web_page_preview=True)
            return
        if raw.lower().startswith("custom"):
            custom = parse_theme_custom_args(raw[6:].strip())
            if not custom:
                await safe_reply(message, "কোন valid custom color পেলাম না। Example: /theme custom bg=#03101F table=#07162D card1=#132744 card2=#0E2037 text=#EAF2FF muted=#B9C7DD subtext=#C8D8F4 accent=#D7F7CC footer=#95A0B4 outline=#18324B")
                return
            row = get_user_visual_row(user.id)
            current_name = (row["theme_name"] if row and row["theme_name"] else "midnight")
            upsert_user_visual(user.id, theme_name=current_name, custom_theme=jdump(custom))
            await safe_reply(message, f"✅ Custom theme saved.\n\n{theme_text_summary(user.id)}", parse_mode=ParseMode.HTML, disable_web_page_preview=True)
            return
        name = raw.lower()
        if name not in BUILTIN_THEMES:
            await safe_reply(message, "Unknown theme. Use: midnight, ocean, emerald, sunset অথবা /theme custom ...")
            return
        upsert_user_visual(user.id, theme_name=name, custom_theme=None)
        await safe_reply(message, f"✅ Theme set to <b>{html_escape(name)}</b>.\n\n{theme_text_summary(user.id)}", parse_mode=ParseMode.HTML, disable_web_page_preview=True)
        return

    if chat.type == "private" and cmd == "setthumb":
        if not user_has_staff_access(user.id):
            await safe_reply(message, warning_text())
            return
        set_user_state(user.id, "await_thumbnail_photo")
        await safe_reply(message, "একটি photo বা image document পাঠান। এটা future PDF report thumbnail হিসেবে ব্যবহার হবে।")
        return

    if chat.type == "private" and cmd == "clearthumb":
        if not user_has_staff_access(user.id):
            await safe_reply(message, warning_text())
            return
        clear_report_thumbnail(user.id)
        await safe_reply(message, "🗑 Custom report thumbnail removed. এখন bot default thumbnail ব্যবহার করবে।")
        return

    if chat.type == "private" and cmd == "thumbstatus":
        if not user_has_staff_access(user.id):
            await safe_reply(message, warning_text())
            return
        row = get_user_visual_row(user.id)
        if row and row["thumb_preview_path"] and Path(str(row["thumb_preview_path"])).exists():
            txt = f"✅ Custom thumbnail active.\nPath: <code>{html_escape(str(row['thumb_preview_path']))}</code>"
            if row["thumb_github_path"]:
                txt += f"\nGitHub: <code>{html_escape(str(row['thumb_github_path']))}</code>"
        else:
            txt = "কোন custom thumbnail set করা নেই। Bot default generated preview ব্যবহার করবে।"
        await safe_reply(message, txt, parse_mode=ParseMode.HTML)
        return

    await _original_handle_text(update, context)

    if cmd in {"addadmin", "rmadmin", "removeadmin", "deladmin"} and chat.type == "private" and is_owner(user.id):
        with suppress(Exception):
            await refresh_scoped_commands(context.bot)


def everyone_private_commands() -> List[BotCommand]:
    return [
        BotCommand("start", "Bot activate / practice open"),
        BotCommand("help", "Help & commands"),
        BotCommand("commands", "Command list"),
        BotCommand("stoptqex", "Stop চলমান practice/exam in PM"),
    ]


def admin_private_commands() -> List[BotCommand]:
    return everyone_private_commands() + [
        BotCommand("panel", "Admin panel"),
        BotCommand("newexam", "Create new exam draft"),
        BotCommand("drafts", "My drafts"),
        BotCommand("csvformat", "CSV import format"),
        BotCommand("setthumb", "Set PDF preview thumbnail"),
        BotCommand("clearthumb", "Clear thumbnail"),
        BotCommand("thumbstatus", "Thumbnail status"),
        BotCommand("cancel", "Cancel current input flow"),
    ]


def owner_private_commands() -> List[BotCommand]:
    return admin_private_commands() + [
        BotCommand("theme", "Leaderboard theme settings"),
        BotCommand("addadmin", "Add bot admin"),
        BotCommand("rmadmin", "Remove bot admin"),
        BotCommand("admins", "List bot admins"),
        BotCommand("audit", "Recent admin actions"),
        BotCommand("logs", "Bot logs summary"),
        BotCommand("broadcast", "Broadcast to groups + users"),
        BotCommand("announce", "Announce to one chat"),
        BotCommand("restart", "Restart bot"),
    ]


def group_admin_commands() -> List[BotCommand]:
    return [
        BotCommand("binddraft", "Bind draft to this group"),
        BotCommand("examstatus", "Current exam/binding status"),
        BotCommand("starttqex", "Ready button / start exam"),
        BotCommand("stoptqex", "Stop running exam"),
        BotCommand("schedule", "Schedule exam"),
        BotCommand("listschedules", "List scheduled exams"),
        BotCommand("cancelschedule", "Cancel schedule"),
    ]


async def refresh_scoped_commands(bot) -> None:
    with suppress(TelegramError):
        await bot.set_my_commands(everyone_private_commands(), scope=BotCommandScopeAllPrivateChats())
    with suppress(TelegramError):
        await bot.set_my_commands(group_admin_commands(), scope=BotCommandScopeAllChatAdministrators())
    for uid in all_admin_ids():
        cmds = owner_private_commands() if is_owner(uid) else admin_private_commands()
        with suppress(TelegramError):
            await bot.set_my_commands(cmds, scope=BotCommandScopeChat(uid))


async def post_init(app: Application) -> None:
    me = await app.bot.get_me()
    app.bot_data["bot_username"] = me.username or ""
    await restore_schedules(app)
    app.job_queue.run_repeating(cleanup_old_data_job, interval=3600, first=300, name="cleanup")
    await refresh_scoped_commands(app.bot)
    logger.info("Bot started as @%s", me.username)


def build_app() -> Application:
    app = (
        ApplicationBuilder()
        .token(CONFIG.bot_token)
        .post_init(post_init)
        .build()
    )

    app.add_handler(CallbackQueryHandler(callback_router), group=0)
    app.add_handler(PollAnswerHandler(handle_poll_answer), group=0)
    app.add_handler(ChatMemberHandler(handle_my_chat_member, chat_member_types=ChatMemberHandler.MY_CHAT_MEMBER), group=0)
    app.add_handler(MessageHandler(filters.StatusUpdate.PINNED_MESSAGE, handle_pinned_service), group=1)
    app.add_handler(MessageHandler(filters.PHOTO, handle_photo_upload), group=1)
    app.add_handler(MessageHandler(filters.Document.ALL, handle_document_upload), group=1)
    app.add_handler(MessageHandler(filters.POLL, handle_poll_import), group=1)
    app.add_handler(MessageHandler(filters.TEXT, handle_text), group=2)
    app.add_handler(MessageHandler(filters.ALL, handle_restriction_and_bookkeeping), group=10)
    app.add_error_handler(error_handler)
    return app



# ============================================================
# HTML + CSS + Playwright renderer (advanced)
# ============================================================

_pillow_render_leaderboard_png = render_leaderboard_png
_pillow_render_report_pdf = render_report_pdf
_FONT_DATA_URI_CACHE: Dict[str, str] = {}


def _font_data_uri(path: Path) -> str:
    import base64
    key = str(path.resolve())
    cached = _FONT_DATA_URI_CACHE.get(key)
    if cached:
        return cached
    data = path.read_bytes()
    ext = path.suffix.lower()
    mime = 'font/ttf' if ext == '.ttf' else 'font/otf'
    uri = f"data:{mime};base64,{base64.b64encode(data).decode('ascii')}"
    _FONT_DATA_URI_CACHE[key] = uri
    return uri


def _html_font_css() -> str:
    faces = []
    mapping = [
        ('AppBengali', FONTS_DIR / 'NotoSansBengali-Regular.ttf', 400),
        ('AppBengali', FONTS_DIR / 'NotoSansBengali-Bold.ttf', 700),
        ('AppSans', FONTS_DIR / 'NotoSans-Regular.ttf', 400),
        ('AppSans', FONTS_DIR / 'NotoSans-Bold.ttf', 700),
        ('AppSymbols', FONTS_DIR / 'NotoSansSymbols2-Regular.ttf', 400),
        ('AppEmoji', FONTS_DIR / 'NotoEmoji-VariableFont_wght.ttf', 400),
        ('AppEmoji', FONTS_DIR / 'NotoEmoji-Regular.ttf', 400),
    ]
    seen = set()
    for family, p, weight in mapping:
        if not p.exists():
            continue
        key = (family, str(p), weight)
        if key in seen:
            continue
        seen.add(key)
        with suppress(Exception):
            faces.append(
                "@font-face{"
                f"font-family:'{family}';"
                f"src:url('{_font_data_uri(p)}') format('truetype');"
                f"font-weight:{weight};font-style:normal;font-display:swap;"
                "}"
            )
    return "\n".join(faces)


def _render_playwright_png_from_html(html_doc: str, width: int = 1600) -> bytes:
    try:
        from playwright.sync_api import sync_playwright
    except Exception as e:
        raise RuntimeError(f'Playwright import failed: {e}')
    with sync_playwright() as pw:
        browser = pw.chromium.launch(headless=True, args=['--no-sandbox', '--disable-dev-shm-usage'])
        page = browser.new_page(viewport={'width': width, 'height': 1200}, device_scale_factor=1)
        page.set_content(html_doc, wait_until='networkidle')
        page.evaluate("""
            () => {
                const root = document.documentElement;
                root.style.background = getComputedStyle(document.body).backgroundColor;
            }
        """)
        png = page.screenshot(type='png', full_page=True)
        browser.close()
        return png


def _render_playwright_pdf_from_html(html_doc: str) -> bytes:
    try:
        from playwright.sync_api import sync_playwright
    except Exception as e:
        raise RuntimeError(f'Playwright import failed: {e}')
    with sync_playwright() as pw:
        browser = pw.chromium.launch(headless=True, args=['--no-sandbox', '--disable-dev-shm-usage'])
        page = browser.new_page(viewport={'width': 1440, 'height': 1600}, device_scale_factor=1)
        page.set_content(html_doc, wait_until='networkidle')
        pdf = page.pdf(
            format='A4',
            print_background=True,
            margin={'top': '14mm', 'right': '10mm', 'bottom': '14mm', 'left': '10mm'},
        )
        browser.close()
        return pdf


def _theme_vars(theme: Dict[str, str]) -> str:
    return ';'.join([
        f"--bg:{theme['bg']}",
        f"--text:{theme['text']}",
        f"--muted:{theme['muted']}",
        f"--table:{theme['table']}",
        f"--card1:{theme['card1']}",
        f"--card2:{theme['card2']}",
        f"--subtext:{theme['subtext']}",
        f"--accent:{theme['accent']}",
        f"--footer:{theme['footer']}",
    ])


def _leaderboard_html(title: str, items: List[Dict[str, Any]], theme: Dict[str, str]) -> str:
    title = normalize_visual_text(title) or 'Exam'
    rows = []
    for idx, item in enumerate(items or [], start=1):
        primary, sub = finalize_render_labels(item.get('name') or 'Unknown', item.get('sub') or '', int(item.get('user_id') or 0) or None)
        score = html_escape(str(item.get('score') or '0.00'))
        card = 'var(--card1)' if idx == 1 else 'var(--card2)'
        rows.append(
            f"<div class='row' style='background:{card}'>"
            f"<div class='rank'>{idx}</div>"
            f"<div class='namecell'><div class='primary'>{html_escape(primary)}</div>"
            + (f"<div class='secondary'>{html_escape(sub)}</div>" if sub else "") +
            "</div>"
            f"<div class='score'>{score}</div>"
            "</div>"
        )
    if not rows:
        rows = ["<div class='row' style='background:var(--card1)'><div class='rank'>1</div><div class='namecell'><div class='primary'>No eligible participants</div></div><div class='score'>0.00</div></div>"]
    return f"""
<!doctype html>
<html><head><meta charset='utf-8'><style>
{_html_font_css()}
:root {{{_theme_vars(theme)}}}
html,body{{margin:0;padding:0;background:var(--bg);color:var(--text);font-family:'AppBengali','AppSans','AppSymbols','AppEmoji',system-ui,sans-serif;}}
.page{{width:1600px;padding:38px 50px 48px 50px;box-sizing:border-box;background:var(--bg);}}
.title{{font-weight:700;font-size:68px;line-height:1.12;letter-spacing:-0.02em;word-break:break-word;}}
.subtitle{{font-size:33px;color:var(--muted);margin-top:8px;}}
.head{{margin-top:36px;background:var(--table);border-radius:24px;display:grid;grid-template-columns:160px 1fr 220px;padding:22px 32px;font-weight:700;font-size:42px;color:#F5F7FF;}}
.rows{{margin-top:18px;display:flex;flex-direction:column;gap:20px;}}
.row{{border-radius:24px;display:grid;grid-template-columns:160px 1fr 220px;align-items:center;padding:18px 34px;min-height:96px;}}
.rank{{font-size:44px;font-weight:700;color:#F8FBFF;}}
.primary{{font-size:39px;line-height:1.12;color:#EDF4FF;white-space:pre-wrap;word-break:break-word;}}
.secondary{{font-size:24px;line-height:1.15;color:var(--subtext);margin-top:4px;white-space:pre-wrap;word-break:break-word;}}
.score{{font-size:48px;font-weight:700;color:var(--accent);text-align:right;}}
.footer{{margin-top:46px;font-size:24px;color:var(--footer);}}
</style></head><body><div class='page'>
<div class='title'>LEADERBOARD — {html_escape(title)}</div>
<div class='subtitle'>Top performers (score includes negative marking)</div>
<div class='head'><div>Rank</div><div>Name</div><div style='text-align:right'>Score</div></div>
<div class='rows'>{''.join(rows)}</div>
<div class='footer'>Generated by {html_escape(CONFIG.brand_name)}</div>
</div></body></html>
"""


def _report_html(title: str, summary: Dict[str, Any], ranking: List[Dict[str, Any]], theme: Dict[str, str]) -> str:
    title = normalize_visual_text(title) or 'Exam'
    rows = []
    for item in (ranking or []):
        primary, sub = finalize_render_labels(item.get('name') or 'Unknown', item.get('sub_name') or '', int(item.get('user_id') or 0) or None)
        rows.append(
            "<tr>"
            f"<td class='center'>{item.get('rank','')}</td>"
            f"<td><div class='primary'>{html_escape(primary)}</div>" + (f"<div class='secondary'>{html_escape(sub)}</div>" if sub else "") + "</td>"
            f"<td class='num ok'>{html_escape(str(item.get('correct',0)))}</td>"
            f"<td class='num bad'>{html_escape(str(item.get('wrong',0)))}</td>"
            f"<td class='num skip'>{html_escape(str(item.get('skipped',0)))}</td>"
            f"<td class='num'>{html_escape(str(item.get('score','0.00')))}</td>"
            "</tr>"
        )
    if not rows:
        rows = ["<tr><td class='center'>1</td><td><div class='primary'>No eligible participants</div></td><td class='num ok'>0</td><td class='num bad'>0</td><td class='num skip'>0</td><td class='num'>0.00</td></tr>"]
    cards = [
        ('Participants', summary.get('participants','0')),
        ('Questions', summary.get('questions','0')),
        ('Average Score', summary.get('average_score','0.00')),
        ('Highest Score', summary.get('highest_score','0.00')),
        ('Lowest Score', summary.get('lowest_score','0.00')),
        ('Negative / Wrong', summary.get('negative_mark','0')),
        ('Started', summary.get('started_at','—')),
        ('Ended', summary.get('ended_at','—')),
    ]
    cards_html = ''.join([f"<div class='kv'><div class='k'>{html_escape(str(k))}</div><div class='v'>{html_escape(str(v))}</div></div>" for k,v in cards])
    return f"""
<!doctype html>
<html><head><meta charset='utf-8'><style>
{_html_font_css()}
:root {{{_theme_vars(theme)}}}
@page {{ size: A4; margin: 14mm 10mm; }}
html,body{{margin:0;padding:0;background:#ffffff;color:#102030;font-family:'AppBengali','AppSans','AppSymbols','AppEmoji',system-ui,sans-serif;-webkit-print-color-adjust:exact;print-color-adjust:exact;}}
.page{{padding:8px 6px 18px 6px;}}
.brand{{font-size:18px;font-weight:700;color:#18324B;}}
.title{{font-size:38px;font-weight:700;line-height:1.15;margin-top:10px;word-break:break-word;}}
.gen{{font-size:13px;color:#6B7A8B;margin-top:4px;}}
.grid{{margin-top:16px;display:grid;grid-template-columns:1fr 1fr;gap:12px;}}
.kv{{border-radius:16px;background:#F6FAFD;border:1px solid #DCE8F2;padding:12px 18px;break-inside:avoid;}}
.k{{font-size:13px;color:#587086;}}
.v{{font-size:16px;font-weight:700;color:#0F2235;margin-top:4px;white-space:pre-wrap;word-break:break-word;}}
.section{{font-size:16px;font-weight:700;color:#18324B;margin-top:18px;margin-bottom:10px;}}
.table{{width:100%;border-collapse:separate;border-spacing:0 8px;table-layout:fixed;}}
.table thead th{{background:var(--table);color:#fff;font-size:12px;padding:10px 10px;text-align:left;}}
.table thead th:first-child{{border-top-left-radius:12px;border-bottom-left-radius:12px;}}
.table thead th:last-child{{border-top-right-radius:12px;border-bottom-right-radius:12px;}}
.table tbody td{{background:#F8FBFE;border-top:1px solid #DFE8F1;border-bottom:1px solid #DFE8F1;padding:10px 10px;font-size:13px;vertical-align:top;word-break:break-word;}}
.table tbody td:first-child{{border-left:1px solid #DFE8F1;border-top-left-radius:10px;border-bottom-left-radius:10px;}}
.table tbody td:last-child{{border-right:1px solid #DFE8F1;border-top-right-radius:10px;border-bottom-right-radius:10px;}}
.center{{text-align:center;}}
.num{{text-align:right;}}
.ok{{color:#1C7C38;font-weight:700;}}
.bad{{color:#B94040;font-weight:700;}}
.skip{{color:#A77412;font-weight:700;}}
.primary{{font-size:13px;color:#102030;line-height:1.12;white-space:pre-wrap;word-break:break-word;}}
.secondary{{font-size:11px;color:#627B90;line-height:1.1;margin-top:2px;white-space:pre-wrap;word-break:break-word;}}
</style></head><body><div class='page'>
<div class='brand'>{html_escape(CONFIG.brand_name)} • Exam Report</div>
<div class='title'>{html_escape(title)}</div>
<div class='gen'>Generated at {html_escape(fmt_dt(now_ts()))}</div>
<div class='grid'>{cards_html}</div>
<div class='section'>Ranking Analysis</div>
<table class='table'>
<thead><tr><th style='width:44px'>#</th><th>Name</th><th style='width:88px'>Correct</th><th style='width:88px'>Wrong</th><th style='width:88px'>Skipped</th><th style='width:110px'>Score</th></tr></thead>
<tbody>{''.join(rows)}</tbody></table>
</div></body></html>
"""


def render_leaderboard_png(title: str, items: List[Dict[str, Any]], theme: Optional[Dict[str, str]] = None) -> bytes:
    chosen = dict(theme or BUILTIN_THEMES['midnight'])
    try:
        return _render_playwright_png_from_html(_leaderboard_html(title, items, chosen), width=1600)
    except Exception as e:
        logger.warning('HTML leaderboard renderer failed, using pillow fallback: %s', e)
        return _pillow_render_leaderboard_png(title, items, chosen)


def render_report_pdf(title: str, summary: Dict[str, Any], ranking: List[Dict[str, Any]], theme: Optional[Dict[str, str]] = None) -> bytes:
    chosen = dict(theme or BUILTIN_THEMES['midnight'])
    try:
        return _render_playwright_pdf_from_html(_report_html(title, summary, ranking, chosen))
    except Exception as e:
        logger.warning('HTML report renderer failed, using pillow fallback: %s', e)
        return _pillow_render_report_pdf(title, summary, ranking, chosen)

def _ensure_event_loop() -> asyncio.AbstractEventLoop:
    """Make PTB work on Python 3.14+ where get_event_loop() may fail on main thread."""
    try:
        loop = asyncio.get_event_loop()
        if loop.is_closed():
            raise RuntimeError("Current event loop is closed")
        return loop
    except RuntimeError:
        loop = asyncio.new_event_loop()
        asyncio.set_event_loop(loop)
        return loop


def main() -> None:
    _ensure_event_loop()
    threading.Thread(target=health_server, args=(CONFIG.port,), daemon=True, name="health-server").start()
    app = build_app()
    app.run_polling(allowed_updates=Update.ALL_TYPES, drop_pending_updates=True, close_loop=False)


if __name__ == "__main__":
    main()
