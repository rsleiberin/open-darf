# Open-DARF Peer Validator — Start Here (No AI Needed)

Congrats, you’re about to run Open-DARF on **your** computer and prove it works.

## You’ll need
- **Windows 10/11** with **Docker Desktop** installed  
- A terminal:
  - **PowerShell** (Windows), or  
  - **Ubuntu on Windows** (WSL) if you like Linux style

## One-line start

### Windows
~~~powershell
powershell -NoProfile -ExecutionPolicy Bypass -File .\scripts\run.ps1
~~~

### Ubuntu/WSL
~~~bash
bash ./scripts/run.sh
~~~

You’ll see `[HB]` heartbeats every ~2s. That means it’s working.  
**Press Ctrl-C anytime** to stop—our scripts quit cleanly.

## What this does
1. Starts databases (MinIO, Qdrant, Postgres) with Docker Compose.  
2. Starts Neo4j cleanly (simple, reliable settings).  
3. Checks health.  
4. Packs “evidence” (logs, versions, small report) into `/results`.

## How to check it worked
- Look for “Stack healthy and Neo4j seeded” in the terminal.
- Open the `results/` folder — you should see a `.tar.gz` or `.zip` evidence file.

## Troubleshooting
- “Port already in use” → close other apps using those ports or rerun after reboot.
- “Health: fail” → run this validator:

~~~bash
bash ./scripts/validator_acceptance.sh
~~~

This prints a simple PASS/FAIL and writes a JSON report you can share.

You’re done! Welcome to the validator crew.
