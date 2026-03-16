# Target Exam Robot — Commands

সব command দুইভাবে কাজ করবে:
- `/command`
- `.command`

## সবাই (Private)
- `/start` — bot activate / result DM enable
- `/help` / `/commands` / `/cmds` — command list

## Admin / Owner (Private)
- `/panel` — owner/admin inline panel
- `/newexam` — new exam draft create
- `/drafts` / `/mydrafts` — my drafts
- `/csvformat` — CSV format help
- `/cancel` / `/cancelstate` — current input flow cancel

## Owner only (Private)
- `/addadmin [user_id]` — add bot admin
- `/rmadmin [user_id]` — remove bot admin
- `/admins` — admin list
- `/audit` — recent admin actions
- `/logs` — memory, uptime, recent errors + full log
- `/broadcast [pin]` — all groups + started users
- `/announce CHAT_ID [pin]` — one target chat

## Group Admin / Bot Admin
- `/binddraft CODE` — bind draft manually to this group
- `/examstatus` — bound draft + active exam status
- `/starttqex` — start exam now
- `/stoptqex` — stop running exam
- `/schedule YYYY-MM-DD HH:MM` — schedule exam
- `/listschedules` / `/schedules` — scheduled exams list
- `/cancelschedule SCHEDULE_ID` / `/unschedule SCHEDULE_ID` — cancel schedule
- `/help` / `/commands` — group command list

## CSV minimum format
Required columns:
- `questions`
- `option1`
- `option2`
- `answer`

Optional columns:
- `option3` ... `option10`
- `explanation`
- `type`
- `section`
- `/announce CHAT_ID` — specific chat এ announce
- `/announce CHAT_ID pin` — specific chat এ pin সহ announce

## Group Admin / Bot Admin (Group)
- `/binddraft CODE` — target group এ draft bind
- `/examstatus` — current bound draft / active exam status
- `/starttqex` — exam শুরু
- `/stoptqex` — exam বন্ধ
- `/schedule YYYY-MM-DD HH:MM` — scheduled exam
- `/listschedules` — scheduled exam list
- `/cancelschedule SCHEDULE_ID` — schedule cancel
- `/help` বা `/commands` — group command list

## Flow
1. PM এ `/newexam`
2. Title → time/question → negative mark দিন
3. Quiz poll forward করুন অথবা CSV upload করুন
4. Group এ `/binddraft CODE`
5. `/starttqex` অথবা `/schedule YYYY-MM-DD HH:MM`
