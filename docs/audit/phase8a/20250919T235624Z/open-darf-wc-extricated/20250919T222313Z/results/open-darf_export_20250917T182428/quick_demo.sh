#!/usr/bin/env bash
set -Eeuo pipefail

echo "=== Open-DARF: 15-Minute Community Validation ==="
echo "Step 1/4 — Infra health (optional containers)"
if command -v docker >/dev/null 2>&1 && docker compose version >/dev/null 2>&1; then
  docker compose up -d || true
else
  echo "Docker not detected; proceeding without containers."
fi
python3 scripts/verify_demo_setup.py || echo "Health check: soft warnings only"

echo "Step 2/4 — Performance demo (small samples)"
python3 scripts/run_performance_demo.py --dataset_sample 100 --constitutional_analysis || true

echo "Step 3/4 — Constitutional framework demo"
python3 scripts/constitutional_demo.py || true

echo "Step 4/4 — Generate results summary"
python3 scripts/generate_results_summary.py || true

echo "=== Done. See ./results and ./docs for artifacts. ==="
