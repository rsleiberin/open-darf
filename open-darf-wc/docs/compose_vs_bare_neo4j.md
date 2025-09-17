# Open-DARF: Compose DBs + Bare-Run Neo4j (Phase 7Y)

**Why this pattern now (Windows-first, peer validators):**
- Docker Compose env-var mapping for Neo4j v5 often injects invalid keys.
- A clean `neo4j:5.15-community` with only `NEO4J_AUTH` avoids startup churn.
- Compose still manages MinIO/Qdrant/Postgres for simplicity.

## Start (Ubuntu shell or WSL)

~~~bash
# DBs via compose; Neo4j bare-run clean; Evidence pack at the end
bash ./scripts/run.sh
~~~

## Start (Windows PowerShell)

~~~powershell
powershell -NoProfile -ExecutionPolicy Bypass -File .\scripts\run.ps1
~~~

## Stop / Cleanup (safe)

~~~bash
# Cancel-safe kill switch; preserves volumes by default
bash ./scripts/kill_switch.sh   # if present; otherwise use the cleanup command provided earlier
~~~

## What “healthy” looks like

- MinIO: ok at http://localhost:9000/minio/health/live  
- Qdrant: ok at http://localhost:6333/healthz  
- Postgres: `pg_isready` returns “accepting connections”  
- Neo4j: `cypher-shell "RETURN 1;"` succeeds

Receipts are written to `open-darf-wc/results/`.
