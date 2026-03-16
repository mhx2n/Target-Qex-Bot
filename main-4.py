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
import time
import uuid
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
for _p in (DATA_DIR, LOG_DIR, TEMP_DIR):
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
    delete_delay_seconds=int(os.getenv("AUTO_DELETE_CONTROL_AFTER", "20")),
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
    if username:
        return f"@{username}"
    full = " ".join(x for x in [first_name, last_name] if x).strip()
    return full or "Unknown User"



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
                CREATE INDEX IF NOT EXISTS idx_answers_session_user ON answers(session_id, user_id);
                CREATE INDEX IF NOT EXISTS idx_schedules_status_time ON schedules(status, run_at);
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
            ])
    else:
        lines.extend([
            "<b>Group Admin / Bot Admin</b>",
            "• /binddraft CODE — bind draft to this group",
            "• /examstatus — current binding/exam status",
            "• /starttqex — start exam now",
            "• /stoptqex — stop running exam",
            "• /schedule YYYY-MM-DD HH:MM — schedule exam",
            "• /listschedules — list scheduled exams",
            "• /cancelschedule SCHEDULE_ID — cancel schedule",
            "• /help or /commands — command list",
        ])
        if is_owner_user:
            lines.extend(["", "<b>Owner</b>", "• /logs — owner gets log summary in PM"])
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
        "/usr/share/fonts/truetype/noto/NotoSans-Regular.ttf",
        "/usr/share/fonts/truetype/noto/NotoSansBengali-Regular.ttf",
        "/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf",
    ],
    "bold": [
        "/usr/share/fonts/truetype/noto/NotoSans-Bold.ttf",
        "/usr/share/fonts/truetype/noto/NotoSansBengali-Bold.ttf",
        "/usr/share/fonts/truetype/dejavu/DejaVuSans-Bold.ttf",
    ],
    "emoji": [
        "/usr/share/fonts/truetype/noto/NotoColorEmoji.ttf",
        "/usr/share/fonts/truetype/noto/NotoEmoji-Regular.ttf",
        "/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf",
    ],
}


def find_font(kind: str, size: int) -> ImageFont.FreeTypeFont | ImageFont.ImageFont:
    for path in FONT_CANDIDATES.get(kind, []):
        if os.path.exists(path):
            with suppress(Exception):
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
    words = text.split()
    if not words:
        return [""]
    lines: List[str] = []
    current = words[0]
    for word in words[1:]:
        trial = f"{current} {word}"
        bbox = draw.textbbox((0, 0), trial, font=font)
        if bbox[2] - bbox[0] <= max_width:
            current = trial
        else:
            lines.append(current)
            current = word
    lines.append(current)
    return lines


def draw_multiline(draw: ImageDraw.ImageDraw, text: str, xy: Tuple[int, int], font, fill, max_width: int, line_gap: int = 10) -> Tuple[int, int]:
    x, y = xy
    lines = wrap_text(draw, text, font, max_width)
    for line in lines:
        draw.text((x, y), line, font=font, fill=fill)
        bbox = draw.textbbox((x, y), line, font=font)
        y += (bbox[3] - bbox[1]) + line_gap
    return x, y


def render_leaderboard_png(title: str, items: List[Dict[str, Any]]) -> bytes:
    width = 1600
    height = 320 + max(1, len(items)) * 128 + 110
    img = Image.new("RGB", (width, height), "#030814")
    draw = ImageDraw.Draw(img)

    title_font = FONTS.get("bold", 70)
    sub_font = FONTS.get("regular", 34)
    head_font = FONTS.get("bold", 42)
    row_font = FONTS.get("regular", 40)
    score_font = FONTS.get("bold", 46)
    small_font = FONTS.get("regular", 24)

    draw.text((60, 38), f"LEADERBOARD — {title}", font=title_font, fill="#E8F0FF")
    draw.text((60, 122), "Top performers (score includes negative marking)", font=sub_font, fill="#B9C7DD")

    table_x = 50
    table_y = 210
    table_w = width - 100
    draw.rounded_rectangle((table_x, table_y, table_x + table_w, table_y + 88), radius=24, fill="#0A1325")
    draw.text((table_x + 32, table_y + 22), "Rank", font=head_font, fill="#F5F7FF")
    draw.text((table_x + 190, table_y + 22), "Name", font=head_font, fill="#F5F7FF")
    draw.text((table_x + table_w - 220, table_y + 22), "Score", font=head_font, fill="#F5F7FF")

    y = table_y + 112
    for idx, item in enumerate(items, start=1):
        fill = "#132744" if idx == 1 else "#10223A"
        draw.rounded_rectangle((table_x, y, table_x + table_w, y + 96), radius=24, fill=fill)
        draw.text((table_x + 34, y + 22), str(idx), font=head_font, fill="#F8FBFF")
        name = item["name"]
        score = item["score"]
        max_name_w = table_w - 520
        lines = wrap_text(draw, name, row_font, max_name_w)
        draw.text((table_x + 185, y + 18), lines[0], font=row_font, fill="#EDF4FF")
        if len(lines) > 1:
            draw.text((table_x + 185, y + 54), lines[1], font=small_font, fill="#D7E5FF")
        draw.text((table_x + table_w - 210, y + 20), score, font=score_font, fill="#D7F7CC")
        y += 118

    draw.text((60, height - 52), f"Generated by {CONFIG.brand_name}", font=small_font, fill="#95A0B4")
    buf = io.BytesIO()
    img.save(buf, format="PNG", optimize=True)
    return buf.getvalue()



def render_report_pdf(title: str, summary: Dict[str, Any], ranking: List[Dict[str, Any]], qstats: List[Dict[str, Any]]) -> bytes:
    pages: List[Image.Image] = []
    width, height = 1600, 2200
    title_font = FONTS.get("bold", 60)
    body_font = FONTS.get("regular", 34)
    sub_font = FONTS.get("regular", 28)
    head_font = FONTS.get("bold", 34)

    def new_page() -> Tuple[Image.Image, ImageDraw.ImageDraw]:
        page = Image.new("RGB", (width, height), "#04101A")
        dr = ImageDraw.Draw(page)
        return page, dr

    # Summary page
    page, dr = new_page()
    dr.text((70, 60), f"Exam Report — {title}", font=title_font, fill="#F0F6FF")
    dr.text((70, 145), "Automatic report for admins and owner", font=body_font, fill="#B8C7D9")
    box = (70, 240, width - 70, 630)
    dr.rounded_rectangle(box, radius=28, fill="#0E2235")
    info_lines = [
        f"Participants: {summary['participants']}",
        f"Questions: {summary['questions']}",
        f"Average Score: {summary['average_score']}",
        f"Highest Score: {summary['highest_score']}",
        f"Lowest Score: {summary['lowest_score']}",
        f"Negative Mark / Wrong: {summary['negative_mark']}",
        f"Started: {summary['started_at']}",
        f"Ended: {summary['ended_at']}",
    ]
    sy = 290
    for line in info_lines:
        dr.text((110, sy), line, font=body_font, fill="#ECF3FF")
        sy += 42
    dr.text((70, 690), "Full Ranking", font=title_font, fill="#F0F6FF")
    pages.append(page)

    # Ranking pages
    rank_chunks = list(chunked(ranking, 28)) or [[]]
    for page_index, chunk in enumerate(rank_chunks, start=1):
        page, dr = new_page()
        dr.text((70, 60), f"Ranking • Page {page_index}/{len(rank_chunks)}", font=title_font, fill="#F0F6FF")
        dr.rounded_rectangle((70, 150, width - 70, 210), radius=18, fill="#0A1325")
        headers = [(110, "#"), (200, "Name"), (1040, "Correct"), (1180, "Wrong"), (1330, "Score")]
        for x, label in headers:
            dr.text((x, 165), label, font=head_font, fill="#F6FAFF")
        y = 235
        for item in chunk:
            dr.rounded_rectangle((70, y, width - 70, y + 60), radius=18, fill="#10223A")
            dr.text((110, y + 12), str(item['rank']), font=body_font, fill="#F0F6FF")
            dr.text((200, y + 12), item['name'][:36], font=body_font, fill="#F0F6FF")
            dr.text((1055, y + 12), str(item['correct']), font=body_font, fill="#D5F6CC")
            dr.text((1195, y + 12), str(item['wrong']), font=body_font, fill="#FFD8D8")
            dr.text((1330, y + 12), item['score'], font=body_font, fill="#F0F6FF")
            y += 72
        pages.append(page)

    # Question analytics pages
    q_chunks = list(chunked(qstats, 32)) or [[]]
    for page_index, chunk in enumerate(q_chunks, start=1):
        page, dr = new_page()
        dr.text((70, 60), f"Question Analytics • Page {page_index}/{len(q_chunks)}", font=title_font, fill="#F0F6FF")
        dr.rounded_rectangle((70, 150, width - 70, 210), radius=18, fill="#0A1325")
        headers = [(110, "Q"), (240, "Correct"), (450, "Wrong"), (620, "Skipped"), (840, "Question Preview")]
        for x, label in headers:
            dr.text((x, 165), label, font=head_font, fill="#F6FAFF")
        y = 235
        for item in chunk:
            dr.rounded_rectangle((70, y, width - 70, y + 60), radius=18, fill="#10223A")
            dr.text((110, y + 12), str(item['q_no']), font=body_font, fill="#F0F6FF")
            dr.text((250, y + 12), str(item['correct']), font=body_font, fill="#D5F6CC")
            dr.text((465, y + 12), str(item['wrong']), font=body_font, fill="#FFD8D8")
            dr.text((640, y + 12), str(item['skipped']), font=body_font, fill="#FFF6C8")
            dr.text((840, y + 12), item['preview'][:38], font=sub_font, fill="#EDF4FF")
            y += 72
        pages.append(page)

    rgb_pages = [p.convert("RGB") for p in pages]
    buf = io.BytesIO()
    rgb_pages[0].save(buf, format="PDF", save_all=True, append_images=rgb_pages[1:])
    return buf.getvalue()

# ============================================================
# Access and exam logic
# ============================================================

async def is_required_channel_member(context: ContextTypes.DEFAULT_TYPE, user_id: int) -> bool:
    channel = CONFIG.required_channel
    if not channel:
        return True
    try:
        member = await context.bot.get_chat_member(channel, user_id)
        return member.status not in {ChatMemberStatus.LEFT, ChatMemberStatus.KICKED}
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



def get_session_ranking(session_id: str) -> List[Dict[str, Any]]:
    session = get_session(session_id)
    if not session:
        return []
    rows = DBH.fetchall(
        "SELECT * FROM participants WHERE session_id=? AND eligible=1 ORDER BY score DESC, correct_count DESC, wrong_count ASC, last_answer_at ASC, user_id ASC",
        (session_id,),
    )
    ranking: List[Dict[str, Any]] = []
    total_questions = int(session["total_questions"])
    for rank, row in enumerate(rows, start=1):
        answered = DBH.fetchone("SELECT COUNT(*) AS c FROM answers WHERE session_id=? AND user_id=?", (session_id, row["user_id"]))
        answered_count = int(answered["c"] if answered else 0)
        ranking.append(
            {
                "rank": rank,
                "user_id": row["user_id"],
                "name": row["display_name"] or row["username"] or str(row["user_id"]),
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
    )
    kb = InlineKeyboardMarkup(
        [
            [
                InlineKeyboardButton("🔄 Set Active", callback_data=f"draft:set:{draft_id}"),
                InlineKeyboardButton("🗑 Delete", callback_data=f"draft:del:{draft_id}"),
            ],
            [InlineKeyboardButton("📋 My Drafts", callback_data="panel:drafts")],
        ]
    )
    await context.bot.send_message(chat_id, text, parse_mode=ParseMode.HTML, reply_markup=kb)


async def notify_admins(context: ContextTypes.DEFAULT_TYPE, text: str) -> None:
    for uid in all_admin_ids():
        row = DBH.fetchone("SELECT started FROM known_users WHERE user_id=?", (uid,))
        if row and int(row["started"]) == 1:
            with suppress(TelegramError):
                await context.bot.send_message(uid, text, parse_mode=ParseMode.HTML)


async def start_exam_countdown(context: ContextTypes.DEFAULT_TYPE, session_id: str) -> None:
    session = get_session(session_id)
    if not session:
        return
    chat_id = int(session["chat_id"])
    countdown = CONFIG.countdown_seconds
    text = (
        f"<b>{html_escape(session['title'])}</b>\n"
        f"Questions: <b>{session['total_questions']}</b>\n"
        f"Time / question: <b>{session['question_time']} sec</b>\n"
        f"Negative / wrong: <b>{session['negative_mark']}</b>\n\n"
        f"Exam starts in <b>{countdown}</b> seconds..."
    )
    msg = await context.bot.send_message(chat_id, text, parse_mode=ParseMode.HTML)
    mark_session_countdown_message(session_id, msg.message_id)
    await safe_pin_message(context.bot, chat_id, msg.message_id)
    await delete_service_pin_later(context, chat_id)
    for sec in range(countdown - 1, -1, -1):
        await asyncio.sleep(1)
        if not get_session(session_id) or get_session(session_id)["status"] != "countdown":
            return
        new_text = text.replace(f"<b>{sec + 1}</b>", f"<b>{sec}</b>") if sec + 1 <= countdown else text
        if sec == 0:
            new_text = (
                f"<b>{html_escape(session['title'])}</b>\n"
                f"Exam is now starting..."
            )
        with suppress(TelegramError):
            await context.bot.edit_message_text(chat_id=chat_id, message_id=msg.message_id, text=new_text, parse_mode=ParseMode.HTML)
    DBH.execute("UPDATE sessions SET status='running', status_message_id=? WHERE id=?", (msg.message_id, session_id))
    context.job_queue.run_once(begin_or_advance_exam_job, when=0.5, data={"session_id": session_id}, name=f"advance:{session_id}")


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
        msg = await context.bot.send_poll(
            chat_id=session["chat_id"],
            question=q["question"],
            options=options,
            type=Poll.QUIZ,
            is_anonymous=False,
            allows_multiple_answers=False,
            correct_option_id=int(q["correct_option"]),
            explanation=q["explanation"] or "",
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
    if not q or not q["message_id"]:
        return
    with suppress(TelegramError):
        await context.bot.stop_poll(chat_id=session["chat_id"], message_id=q["message_id"])
    set_session_active_poll(session_id, None, None)
    context.job_queue.run_once(begin_or_advance_exam_job, when=1, data={"session_id": session_id}, name=f"advance:{session_id}")


async def finish_exam(context: ContextTypes.DEFAULT_TYPE, session_id: str, reason: str = "completed") -> None:
    session = get_session(session_id)
    if not session or session["status"] in {"finished", "stopped"}:
        return
    chat_id = int(session["chat_id"])
    if session["active_poll_message_id"]:
        with suppress(TelegramError):
            await context.bot.stop_poll(chat_id=chat_id, message_id=int(session["active_poll_message_id"]))
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
    leaderboard_rows = [{"name": item["name"], "score": item["score"]} for item in top]
    image_bytes = render_leaderboard_png(session["title"], leaderboard_rows or [{"name": "No eligible participants", "score": "0.00"}])
    await context.bot.send_chat_action(chat_id=chat_id, action=ChatAction.UPLOAD_PHOTO)
    await context.bot.send_photo(chat_id=chat_id, photo=InputFile(io.BytesIO(image_bytes), filename="leaderboard.png"), caption=f"🏁 {session['title']} finished.")

    # per-user DM results
    await send_private_results(context, session_id)

    # send pdf if more than top_n participants
    if len(ranking) > CONFIG.scoreboard_top_n:
        await send_admin_pdf_report(context, session_id, ranking)

    # cleanup binding + draft so new exam must be created again
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
    started_admins = []
    for uid in all_admin_ids():
        row = DBH.fetchone("SELECT started FROM known_users WHERE user_id=?", (uid,))
        if row and int(row["started"]) == 1:
            started_admins.append(uid)
    for uid in started_admins:
        with suppress(TelegramError):
            await context.bot.send_document(
                uid,
                document=InputFile(io.BytesIO(pdf_bytes), filename=f"{session['title']}_report.pdf"),
                caption=f"📄 {session['title']} report",
            )


async def send_private_results(context: ContextTypes.DEFAULT_TYPE, session_id: str) -> None:
    session = get_session(session_id)
    if not session:
        return
    chat_row = DBH.fetchone("SELECT username FROM known_chats WHERE chat_id=?", (session["chat_id"],))
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
                disable_web_page_preview=True,
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
    ]
    if is_owner_user:
        rows.append([InlineKeyboardButton("👥 Admins", callback_data="panel:admins"), InlineKeyboardButton("📋 Logs", callback_data="panel:logs")])
        rows.append([InlineKeyboardButton("📢 Broadcast Help", callback_data="panel:broadcast")])
    return InlineKeyboardMarkup(rows)


async def send_panel(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    user = update.effective_user
    if not user:
        return
    text = (
        f"<b>{CONFIG.brand_name}</b>\n\n"
        f"এই bot এ exam draft তৈরি, quiz forward/import, group bind, start/stop, schedule, leaderboard image, PDF report, DM result, logs, broadcast—সব আছে।\n\n"
        f"<b>Quick flow</b>\n"
        f"1) New Exam\n"
        f"2) Quiz forward / CSV upload\n"
        f"3) Target group এ <code>.binddraft CODE</code>\n"
        f"4) <code>.starttqex</code> বা <code>.schedule YYYY-MM-DD HH:MM</code>\n\n"
        f"সব group command <b>/</b> এবং <b>.</b> — দুই prefix এই কাজ করবে।"
    )
    await context.bot.send_message(user.id, text, parse_mode=ParseMode.HTML, reply_markup=panel_keyboard(is_owner(user.id)))


async def show_groups(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    rows = DBH.fetchall("SELECT * FROM known_chats WHERE active=1 AND chat_type IN ('group','supergroup') ORDER BY title COLLATE NOCASE ASC")
    if not rows:
        text = "কোনো known group এখনও নেই। Bot-কে আগে group-এ add করুন।"
    else:
        lines = ["<b>Known Groups</b>"]
        for row in rows[:50]:
            lines.append(f"• <b>{html_escape(row['title'])}</b> — <code>{row['chat_id']}</code>")
        text = "\n".join(lines)
    target = update.effective_user.id if update.effective_user else update.effective_chat.id
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
    if data == "panel:new":
        set_user_state(user.id, "await_title")
        await query.message.reply_text("Exam title পাঠান।")
        return
    if data == "panel:drafts":
        await show_drafts(update, context, user.id)
        return
    if data == "panel:groups":
        await show_groups(update, context)
        return
    if data == "panel:schedules":
        rows = DBH.fetchall(
            "SELECT s.*, d.title FROM schedules s JOIN drafts d ON d.id=s.draft_id WHERE s.status='scheduled' ORDER BY s.run_at ASC LIMIT 20"
        )
        if not rows:
            await query.message.reply_text("কোন scheduled exam নেই।")
        else:
            lines = ["<b>Scheduled Exams</b>"]
            for row in rows:
                lines.append(f"• <code>{row['id']}</code> — {html_escape(row['title'])} — {fmt_dt(row['run_at'])} — chat <code>{row['chat_id']}</code>")
            await query.message.reply_text("\n".join(lines), parse_mode=ParseMode.HTML)
        return
    if data == "panel:admins":
        if not is_owner(user.id):
            await query.message.reply_text("Only owner can view admins.")
            return
        await show_admins(update, context)
        return
    if data == "panel:logs":
        if not is_owner(user.id):
            await query.message.reply_text("Only owner can view logs.")
            return
        await show_logs(update, context)
        return
    if data == "panel:broadcast":
        if not is_owner(user.id):
            return
        text = (
            "Reply to any message in your PM with:\n"
            "<code>/broadcast</code> or <code>.broadcast</code> → all groups + started users\n"
            "<code>/broadcast pin</code> → groups only pin too\n"
            "<code>/announce CHAT_ID pin</code> → one target chat"
        )
        await query.message.reply_text(text, parse_mode=ParseMode.HTML)
        return
    if data.startswith("draft:set:"):
        draft_id = data.split(":", 2)[2]
        draft = get_draft(draft_id)
        if not draft or int(draft["owner_id"]) != user.id:
            await query.message.reply_text("এই draft পাওয়া যায়নি।")
            return
        set_active_draft(user.id, draft_id)
        await send_draft_card(context, user.id, user.id, draft_id, header="✅ Active draft updated")
        return
    if data.startswith("draft:del:"):
        draft_id = data.split(":", 2)[2]
        draft = get_draft(draft_id)
        if not draft:
            await query.message.reply_text("Draft already deleted.")
            return
        if int(draft["owner_id"]) != user.id and not is_owner(user.id):
            await query.message.reply_text("এই draft delete করার অনুমতি নেই।")
            return
        delete_draft(draft_id, user.id)
        await query.message.reply_text("🗑 Draft deleted.")
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

    # universal private /start with join gate
    if command == "start":
        mark_started(user)
        if chat.type == "private":
            joined = await is_required_channel_member(context, user.id)
            if not joined:
                kb = InlineKeyboardMarkup([[InlineKeyboardButton("Join Required Channel", url=f"https://t.me/{CONFIG.required_channel.lstrip('@')}")]])
                await safe_reply(message, f"এই bot ব্যবহার করতে আগে {CONFIG.required_channel} channel এ join করুন। তারপর আবার /start দিন।", reply_markup=kb)
                return
            await send_panel(update, context)
        else:
            await safe_reply(message, "Private এ /start দিয়ে bot activate করুন।")
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
    if chat.type == "private" and command == "panel":
        if is_bot_admin(user.id):
            await send_panel(update, context)
        else:
            await safe_reply(message, "Bot activate হয়েছে। Exam result DM পেতে পারবেন।")
        return

    if chat.type == "private" and command == "newexam":
        if not is_bot_admin(user.id):
            await safe_reply(message, "শুধু owner/admin exam তৈরি করতে পারবে।")
            return
        set_user_state(user.id, "await_title")
        await safe_reply(message, "Exam title পাঠান।")
        return

    if chat.type == "private" and command in {"mydrafts", "drafts"}:
        if not is_bot_admin(user.id):
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
        if not await is_group_admin_or_global(update, context):
            await safe_reply(message, "শুধু group admin / bot admin exam start করতে পারবে।")
            return
        if get_active_session(chat.id):
            await safe_reply(message, "এই group এ আগে থেকেই একটি exam চলছে।")
            return
        session_id = create_session_from_bound_draft(chat.id, user.id)
        if not session_id:
            await safe_reply(message, "আগে একটি ready draft bind করুন।")
            return
        await start_exam_countdown(context, session_id)
        await safe_reply(message, "🚀 Exam start sequence initiated.")
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
        return

    if command == "schedule":
        if not await is_group_admin_or_global(update, context):
            await safe_reply(message, "শুধু group admin / bot admin schedule করতে পারবে।")
            return
        bound = get_bound_draft(chat.id)
        if not bound:
            await safe_reply(message, "আগে .binddraft CODE দিন।")
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
            (qrow["session_id"], user.id, user.username, choose_name(user.username, user.first_name, user.last_name), now_ts()),
        )
        return
    selected = int(answer.option_ids[0])
    is_correct_ans = 1 if selected == int(qrow["correct_option"]) else 0
    neg = float(qrow["negative_mark"])
    delta = 1.0 if is_correct_ans else (-neg)
    display_name = choose_name(user.username, user.first_name, user.last_name)
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
    logger.exception("Unhandled error", exc_info=context.error)


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
