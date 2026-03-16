# Command List

সব command `/` এবং `.` — দুই prefix এই কাজ করবে।

## সবার জন্য (Private)
- `/start` — বট activate করবে, DM result enable করবে
- `/help` বা `/commands` — command list দেখাবে

## Admin / Owner (Private)
- `/panel` — button based admin panel
- `/newexam` — নতুন exam draft তৈরি
- `/drafts` বা `/mydrafts` — নিজের draft list
- `/csvformat` — CSV header format দেখাবে
- `/cancel` — চলমান input flow cancel করবে

## Owner only (Private)
- `/addadmin USER_ID` — bot admin add
- `/rmadmin USER_ID` — bot admin remove
- `/admins` — admin list
- `/audit` — recent admin action log
- `/logs` — memory, uptime, last-hour error summary + full log file
- `/broadcast` — সব known group + started user inbox এ broadcast
- `/broadcast pin` — group এ pin সহ broadcast
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
