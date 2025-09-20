# Open-DARF Quickstart (Peer Validator)

**Goal:** Run the validator on your machine with one command, watch heartbeats every ~2s, and produce evidence receipts in `results/`.

**Prereqs**
- Docker Desktop (Windows or macOS) or Docker Engine (Linux)
- Git
- (Windows) PowerShell 7+ recommended

**One-liner (Linux/macOS)**
~~~bash
bash ./scripts/run.sh
~~~

**One-liner (Windows PowerShell)**
~~~powershell
powershell -NoProfile -ExecutionPolicy Bypass -File .\scripts\run.ps1
~~~

**What you’ll see**
- Heartbeats like `[HB] step — 12:34:56`
- Bounded waits (no infinite spinners; Ctrl-C cancels immediately)
- Receipts written to `./results/` (JSON + archives)

**How it works**
- MinIO & Postgres via Compose with **ephemeral ports** (avoids collisions)
- Qdrant & Neo4j run as **bare containers** with ephemeral ports
- Ports are discovered via `docker inspect` and saved to a receipt

**Troubleshooting**
- If a port conflict ever appears, run:
~~~bash
bash ./scripts/kill_switch.sh
~~~
- Then re-run the one-liner above.
