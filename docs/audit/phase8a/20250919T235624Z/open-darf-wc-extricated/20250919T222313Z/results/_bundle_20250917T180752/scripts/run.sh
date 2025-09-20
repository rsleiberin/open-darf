#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
source "./scripts/_hb.sh"

echo "===\n===\n==="
echo "=== Open-DARF · One-line (Linux) — compose DB + clean Neo4j + evidence ==="

if docker compose version >/dev/null 2>&1; then DC="docker compose"; else DC="docker-compose"; fi
hb_start "compose up -d (minio qdrant postgres)"
$DC up -d minio qdrant postgres
hb_stop

# Bare-run Neo4j clean
docker ps -aq --filter "name=^darf-neo4j$" | xargs -r docker rm -f >/dev/null 2>&1 || true
docker volume create open-darf_neo4j_data >/dev/null 2>&1 || true
docker volume create open-darf_neo4j_logs >/dev/null 2>&1 || true
hb_start "docker run neo4j clean"
docker run -d --name darf-neo4j --network open-darf_default --network-alias neo4j \
  -p 7474:7474 -p 7687:7687 \
  -v open-darf_neo4j_data:/data -v open-darf_neo4j_logs:/logs \
  -e NEO4J_AUTH=neo4j/darf_graph_password neo4j:5.15-community >/dev/null
hb_stop

# Quick bounded waits (no long block)
for i in {1..15}; do
  ok_bolt=1
  docker exec darf-neo4j cypher-shell -u neo4j -p darf_graph_password "RETURN 1;" >/dev/null 2>&1 && { ok_bolt=0; break; }
  hb_start "neo4j bolt probe $i/15"; sleep 2; hb_stop
done

# Evidence pack
bash ./scripts/evidence_pack.sh
