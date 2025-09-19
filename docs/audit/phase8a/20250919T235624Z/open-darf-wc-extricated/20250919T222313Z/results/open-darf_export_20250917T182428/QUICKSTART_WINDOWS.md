# Open-DARF — Windows Quickstart (beginner friendly)

Welcome! This guide assumes you've never used a code terminal before. Follow *exactly*.

## Step 0 — One-time setup
1. Open the **Microsoft Store**, install **"Windows Subsystem for Linux" (WSL)** and **Ubuntu**.
2. Install **Docker Desktop for Windows**. In Settings → **Resources → WSL integration**, enable Ubuntu.

## Step 1 — Get the code
Open **PowerShell** (press Start, type "PowerShell", hit Enter), then run:
~~~powershell
# Choose a folder you recognize (e.g., your Desktop)
cd $HOME\Desktop
git clone https://github.com/rsleiberin/open-darf.git
cd open-darf
~~~

If you’re asked to install Git, install it and run those lines again.

## Step 2 — Start the validator (Windows first)
Still in **PowerShell**, run:
~~~powershell
# This installs what you need and starts the validator with friendly heartbeats
powershell -NoProfile -ExecutionPolicy Bypass -File .\scripts\run.ps1
~~~

You’ll see lines every ~2 seconds telling you what’s happening. If you want to stop, press **Ctrl + C**.

## Step 3 — What you should see
- **MinIO**: “ok”
- **Qdrant**: “ok”
- **Postgres**: “ok”
- **Neo4j**: “ok”
- **PASS : true**

If any line is not “ok”, run:
~~~powershell
# Stops everything and frees ports
powershell -NoProfile -ExecutionPolicy Bypass -File .\scripts\kill_switch.ps1
# Then try again:
powershell -NoProfile -ExecutionPolicy Bypass -File .\scripts\run.ps1
~~~

## Step 4 — Learn as you go
Open `docs\learning\lesson_01_introduction.md` in any editor and follow the lessons.
