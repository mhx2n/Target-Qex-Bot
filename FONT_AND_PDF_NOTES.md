# Font + PDF notes

## Repo structure

Keep these files in the repo root or alongside `main.py`:

- `main.py`
- `requirements.txt`
- `render.yaml` or start command on Render
- `fonts/`
  - `NotoSansBengali-Regular.ttf`
  - `NotoSansBengali-Bold.ttf`
  - `NotoSans-Regular.ttf`
  - `NotoSans-Bold.ttf`

Optional:
- `NotoColorEmoji.ttf`
- `HindSiliguri-Regular.ttf`
- `HindSiliguri-Bold.ttf`

## Why PDF may not arrive in owner inbox

Common reasons:
1. Owner/creator did not start the bot in PM before the exam ended.
2. Bot is running in more than one instance and polling conflicts happen.
3. The bot tried to render/send the report but Telegram rejected a PM send.
4. The service restarted before the report finished sending.

## What changed in this build

- Bot now checks `fonts/` inside the repo first.
- The ready/start message is edited in place instead of sending a fresh pinned status message.
- `.starttqex DRAFTCODE` is supported.
- The PDF layout uses a white background and clearer tables.
- Extra logging was added before PDF send attempts.
