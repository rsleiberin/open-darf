# Open-DARF · Peer Validator (Windows-first)

This guide assumes you’ve **never** used a code terminal.

## What you’ll get
- A one-command validator that brings up local services with **2s heartbeats** and **instant cancel**.
- Clear receipts in `results/` proving what ran on **your** machine.

## Requirements (Windows)
1. **Windows 10/11** with **WSL** (Ubuntu)  
   Open PowerShell as Administrator and run:
~~~powershell
wsl --install -d Ubuntu
~~~
2. **Docker Desktop for Windows**  
   - Install it (default settings).  
   - In Docker Desktop → **Settings → Resources → WSL Integration**, enable **Ubuntu**.
3. **Git for Windows**

> If you already have WSL + Docker Desktop working, you’re good.

---

## Get the code
Open **PowerShell** (regular, not admin) and run:
~~~powershell
cd $HOME\Desktop
git clone https://github.com/rsleiberin/open-darf.git
cd open-darf
~~~

## Run the validator (Windows-first)
~~~powershell
powershell -NoProfile -ExecutionPolicy Bypass -File .\scripts\run.ps1
~~~
- You’ll see a heartbeat every ~2s.  
- To stop at any time, press **Ctrl+C** (cancel-safe).

## If something looks stuck
~~~powershell
powershell -NoProfile -ExecutionPolicy Bypass -File .\scripts\kill_switch.ps1
powershell -NoProfile -ExecutionPolicy Bypass -File .\scripts\run.ps1
~~~

## What’s running
- **MinIO** (object storage)
- **Postgres** (SQL DB)
- **Qdrant** (vector DB)
- **Neo4j** (graph DB — runs “bare” to avoid compose env pitfalls)

The validator auto-detects ports and prints them.

## Where to look
- Health receipts and evidence archives are written under `results/`.
- Learning walkthroughs live in `docs/learning/`.

## FAQ (quick)
**Q: Docker says a port is already in use.**  
A: Run the kill switch above; we remap to free ports automatically.

**Q: How do I re-run cleanly?**  
A: Use kill switch, then run again. Heartbeats confirm progress every ~2s.

**Q: Can I use Linux instead of Windows?**  
A: Yes. Use `bash ./scripts/run.sh`.

---

## Next steps
- Read `docs/learning/lesson_01_introduction.md`
- Share the `results/*.tar.gz` evidence with your peer reviewers.
