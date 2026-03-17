# Commands

সব command `/` এবং `.` — দুই prefix এই কাজ করবে।

## Everyone (Private)
- `/start` — bot activate / result DM enable
- `/start practice_TOKEN` — practice exam start
- `/help` or `/commands` — command list

## Admin / Owner (Private)
- `/panel` — button panel
- `/newexam` — new draft create
- `/drafts` or `/mydrafts` — my drafts
- `/csvformat` — CSV import format
- `/cancel` — current input flow cancel

## Owner Only (Private)
- `/addadmin USER_ID` — add bot admin
- `/rmadmin USER_ID` — remove bot admin
- `/admins` — admin list
- `/audit` — recent admin actions
- `/logs` — memory, uptime, recent errors + full log
- `/broadcast [pin]` — send to all groups + started users
- `/announce CHAT_ID [pin]` — send to one target chat
- `/restart` — restart bot process

## Group Admin / Bot Admin
- `/binddraft CODE` — bind draft manually
- `/examstatus` — current binding / running exam status
- `/starttqex` — start active/bound draft with ready button
- `/starttqex DRAFTCODE` — start a specific draft code with ready button
- `/stoptqex` — stop running exam
- `/schedule YYYY-MM-DD HH:MM` — schedule exam
- `/listschedules` — list schedules
- `/cancelschedule SCHEDULE_ID` — cancel schedule

## Notes
- Non-admin users group-এ command দিলে bot message delete করার চেষ্টা করবে এবং temporary warning দেবে.
- Group exam start হওয়ার ready button সবাই press করতে পারবে.
- Practice link draft card-এ দেখাবে, এবং প্রতি user max 3 attempts পাবে.
- PDF report owner/admin inbox-এ যায় যদি তারা bot-কে private এ আগে `/start` দিয়ে থাকে.
