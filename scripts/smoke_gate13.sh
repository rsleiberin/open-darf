#!/usr/bin/env bash
if [ -x ".venv/bin/python" ]; then export PATH="$(pwd)/.venv/bin:$PATH"; fi
set -e -o pipefail
REPO_TOP="$(git rev-parse --show-toplevel)"
cd "$REPO_TOP"

# load env if present
if [ -f .env.local ]; then set -a; . ./.env.local; set +a; fi

# tools
if ! command -v jq >/dev/null 2>&1; then
  echo "[setup] installing jq…"
  sudo apt-get update -y && sudo apt-get install -y jq
fi

# one-time schema
python apps/validator/init_schema.py >/dev/null && echo "[neo4j] schema: ok"

# latest draft or create demo
LATEST_DRAFT="$(ls -1t var/drafts/*.json 2>/dev/null | head -n 1 || true)"
if [ -z "${LATEST_DRAFT:-}" ]; then
  echo "[demo] creating /tmp/demo_ingest.txt"
  cat > /tmp/demo_ingest.txt <<'EOF'
sovereignty preserved by span-first addressing
capability enhanced via semantic retrieval
transparency guaranteed with hover-to-verify
revocation authority remains with the user
EOF
  echo "[ingest] running…"
  python apps/transform/ingest.py --file /tmp/demo_ingest.txt --user u123 --auth-class owner | tee /tmp/ingest_out.json
  LATEST_DRAFT="$(jq -r '.draft.draft_path' /tmp/ingest_out.json)"
else
  echo "[resume] using latest draft: $LATEST_DRAFT"
fi

echo "[show]"
python apps/transform/show.py --draft "$LATEST_DRAFT"

echo "[validate] strict (no spans)"
python apps/validator/validator.py --draft "$LATEST_DRAFT" --strict --no-spans | tee /tmp/validate_nospans.json

echo "[validate] strict (max 10 spans)"
python apps/validator/validator.py --draft "$LATEST_DRAFT" --strict --max-spans 10 | tee /tmp/validate_spans10.json

LATEST_AUDIT="$(ls -1t var/audit 2>/dev/null | head -n 1 || true)"
if [ -n "${LATEST_AUDIT:-}" ]; then
  echo "--- var/audit/$LATEST_AUDIT ---"
  cat "var/audit/$LATEST_AUDIT"
else
  echo "WARN: no audit files in var/audit"
fi

echo "[smoke] done."
