#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
source "./scripts/_hb.sh"

printf "===\n===\n===\n"
echo "=== Open-DARF · Validator Acceptance (Linux) ==="

RESULTS="results"
mkdir -p "$RESULTS"

# Bounded checks with small time budget (Ctrl-C cancels)
MAX=15 # ~30s
ok_minio="fail"; ok_qdrant="fail"; ok_pg="fail"; ok_neo="fail"

for i in $(seq 1 "$MAX"); do
  hb_start "acceptance $i/$MAX"

  curl -fsS http://localhost:9000/minio/health/live >/dev/null 2>&1 && ok_minio="ok" || true
  curl -fsS http://localhost:6333/healthz           >/dev/null 2>&1 && ok_qdrant="ok" || true
  docker exec darf-postgres pg_isready -U darf_user -d darf_audit >/dev/null 2>&1 && ok_pg="ok" || true
  docker exec darf-neo4j cypher-shell -u neo4j -p darf_graph_password "RETURN 1;" >/dev/null 2>&1 && ok_neo="ok" || true

  hb_stop
  [ "$ok_minio" = "ok" ] && [ "$ok_qdrant" = "ok" ] && [ "$ok_pg" = "ok" ] && [ "$ok_neo" = "ok" ] && break
done

pass="false"
if [ "$ok_minio" = "ok" ] && [ "$ok_qdrant" = "ok" ] && [ "$ok_pg" = "ok" ] && [ "$ok_neo" = "ok" ]; then
  pass="true"
fi

echo "=== Acceptance Summary ==="
printf "MinIO   : %s\n" "$ok_minio"
printf "Qdrant  : %s\n" "$ok_qdrant"
printf "Postgres: %s\n" "$ok_pg"
printf "Neo4j   : %s\n" "$ok_neo"
echo "PASS     : $pass"

# Write JSON receipt (tolerate missing jq)
if command -v jq >/dev/null 2>&1; then
  jq -n --arg ts "$(date -Is)" \
        --arg minio "$ok_minio" --arg qdrant "$ok_qdrant" --arg postgres "$ok_pg" --arg neo4j "$ok_neo" \
        --arg pass "$pass" \
        '{ts:$ts, minio:$minio, qdrant:$qdrant, postgres:$postgres, neo4j:$neo4j, pass:($pass=="true")}' \
        > "$RESULTS/validator_acceptance_report.json"
else
  printf '{"ts":"%s","minio":"%s","qdrant":"%s","postgres":"%s","neo4j":"%s","pass":%s}\n' \
    "$(date -Is)" "$ok_minio" "$ok_qdrant" "$ok_pg" "$ok_neo" "$pass" > "$RESULTS/validator_acceptance_report.json"
fi

[ "$pass" = "true" ] || exit 2
