# Phase 7Y — Implementation Agent 7Y Handoff (Days 1–3)

## What peers get (Windows-first)
- One-line start (PowerShell or Ubuntu/WSL)
- 2s heartbeats in all human-facing scripts
- Cancel-safe flows (Ctrl-C stops immediately)
- Evidence archives + manifest for publishing

## Run it

### Windows
~~~powershell
powershell -NoProfile -ExecutionPolicy Bypass -File .\scripts\run.ps1
~~~

### Ubuntu / WSL
~~~bash
bash ./scripts/run.sh
~~~

## Health pattern (compose DBs + bare Neo4j)
- Compose: MinIO, Qdrant, Postgres
- Bare-run: Neo4j with only NEO4J_AUTH

## Acceptance
~~~bash
bash ./scripts/validator_acceptance.sh
~~~

Outputs JSON receipt in `results/`.

## Artifacts
- Bundle builder (zip): `scripts/build_peer_bundle.*`
- Evidence publisher (manifest + checksum): `scripts/ci_evidence.*`
- Kill switch: `scripts/kill_switch.*`
- Port inspector: `scripts/check_ports.sh`
- Learning module: `docs/learning/*`, launchers `scripts/learn.*`

## Today’s receipts
See `results/day1_3_summary.json` and `results/publish/evidence_manifest.json`.

## Open items (carry to next phase)
- Final editorial pass on docs/screenshots
- Optional: strict Compose-only path once Neo4j env friction is resolved
