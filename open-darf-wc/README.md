# Open-DARF — Peer Validator

Welcome! This repo is set up so anyone (yes, you) can run the **Open-DARF peer validator** on a Windows machine (PowerShell) or Ubuntu/WSL, learn what’s happening, and produce an evidence bundle.

## Quick Start

### Windows (PowerShell)
~~~powershell
powershell -NoProfile -ExecutionPolicy Bypass -File .\scripts\run.ps1
~~~

### Ubuntu / WSL (Ubuntu shell)
~~~bash
bash ./scripts/run.sh
~~~

You’ll see a `[HB]` heartbeat every ~2 seconds. **Ctrl-C** cancels cleanly.

## What gets started

- **Compose**: MinIO, Qdrant, Postgres  
- **Bare-run**: Neo4j (simple & reliable settings)

Health checks run automatically; then an **evidence archive** is written to `results/`.

## Troubleshooting

- **Kill everything** (keeps volumes):  
  ~~~bash
  bash ./scripts/kill_switch.sh
  ~~~
- **See who holds a port**:  
  ~~~bash
  bash ./scripts/check_ports.sh
  ~~~

## Validate your setup

~~~bash
bash ./scripts/validator_acceptance.sh
~~~

This prints a PASS/FAIL and writes a JSON receipt to `results/`.

## Learn the why

- `docs/compose_vs_bare_neo4j.md` — why we use Compose DBs + bare Neo4j  
- `docs/peer_validator_onboarding.md` — step-by-step teen-friendly guide
