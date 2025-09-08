#!/usr/bin/env bash
set -Eeuo pipefail
echo "=== DARF Packaging/Lifecycle Smoke ==="

# 0) Config/Artifacts check
python3 scripts/config_validate.py || { echo "Config validation failed"; exit 2; }
for p in packages/darf_config/settings.py compose/compose.yaml configs/.env.sample; do
  [ -f "$p" ] || { echo "Missing artifact: $p"; exit 3; }
done

# 1) Optional: probe local Neo4j container via podman (non-fatal if absent)
if command -v podman >/dev/null 2>&1; then
  CID="$(podman ps --format '{{.ID}} {{.Names}}' | awk '/neo4j/{print $1; exit}' || true)"
  if [ -n "$CID" ]; then
    echo "[neo4j] probing container: $CID"
    set +e
    podman exec "$CID" bash -lc 'echo "name, version"; /var/lib/neo4j/bin/cypher-shell -u ${NEO4J_user:-neo4j} -p ${NEO4J_password:-neo4j} -f - <<< "CALL dbms.components()" 2>/dev/null | head -n 2'
    RC_NEO=$?
    set -e
    echo "[neo4j] probe_rc=$RC_NEO"
  else
    echo "[neo4j] container not found; skipping."
  fi
else
  echo "[neo4j] podman not available; skipping."
fi

# 2) Always: run RE CI smoke (enforces F1>=0.20 & compliance>=0.95)
python3 scripts/relex_ci_smoke.py
echo "OK: packaging/lifecycle smoke passed."
