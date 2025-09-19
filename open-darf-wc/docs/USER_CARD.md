# Open-DARF Peer Validator — Quick Start (90-Second Card)

**What you’ll do**
- Ensure Docker Desktop (Windows) / Docker Engine (Linux) is running.
- Copy `.env.sample` to `.env` and set your local passwords (they stay on your machine).
- Start databases (Postgres/Redis/Qdrant/Neo4j/MinIO) with a single command.

**What you’ll see**
- Docker pulls images (first run), then shows healthy containers.
- A local evidence/receipts folder appears under `docs/audit/…`.

**If something fails**
- Re-run the start command.
- Check `docs/audit/…/summary.txt` for hints.
- If a port conflict occurs, stop other apps using those ports.

**Stop / Clean up**
- Use the provided stop script or `docker compose down` in this folder.

> Privacy note: This project runs locally. Nothing is uploaded unless you explicitly choose to publish evidence.
