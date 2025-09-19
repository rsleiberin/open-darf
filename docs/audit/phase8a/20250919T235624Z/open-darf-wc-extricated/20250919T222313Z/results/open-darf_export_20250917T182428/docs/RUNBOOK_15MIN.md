# Open-DARF 15-Minute Runbook

Goal: Validate the constitutional demo and performance harness within ~15 minutes on a 10 GB GPU (CPU fallback supported).

## Prerequisites
- Python 3.8+ available on PATH.
- Optional: Docker with Compose (used to spin up Redis, Postgres, Neo4j, Qdrant, MinIO).
- Internet only needed for pulling containers on first run.

## Quick Start
1. Clone and enter the repo:
    git clone https://github.com/rsleiberin/open-darf.git
    cd open-darf

2. (Optional) Start containers:
    docker compose up -d

   If a default port is busy (for example, 5432 for Postgres), this repo uses a local-only
   file named docker-compose.override.yml to remap host ports automatically.
   A ports receipt is saved at results/ports_live_receipt.json for reproducibility.

3. Run the demo:
    bash ./quick_demo.sh

4. Inspect artifacts:
    ls -lah results
    cat results/summary.json

Expected outcomes:
- results/performance_metrics.json reports small-sample F1s.
- results/constitutional_decisions.json reports governance metrics.
- results/summary.json aggregates the above.
- grant_evidence_package.tar.gz (if created) bundles docs and results.

## Troubleshooting
- If Docker is unavailable, the demo falls back to Python-only mode.
- If a port conflict occurs, re-run the setup scripts; they will rewrite the override file.
- Use results/health_report.json and results/ports_live_receipt.json when filing validation reports.

## Reproducibility Checklist
- Record OS, CPU, GPU (VRAM), Python version, Docker version.
- Attach results/summary.json and results/ports_live_receipt.json to your report.
- Note run duration and whether GPU was used.
