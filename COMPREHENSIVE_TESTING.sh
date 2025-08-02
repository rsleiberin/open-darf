#!/bin/bash
set -e

echo "=== DARF Comprehensive Metrics Collection ==="
echo "Collecting all measurable performance data for grant evidence"
echo ""

RESULTS_FILE="var/receipts/open-darf/comprehensive_metrics_$(date +%Y%m%d_%H%M%S).json"

echo "{"
echo "  \"test_metadata\": {"
echo "    \"timestamp\": \"$(date -u +%Y-%m-%dT%H:%M:%SZ)\","
echo "    \"platform\": \"$(uname -s)\","
echo "    \"hostname\": \"$(hostname)\","
echo "    \"test_duration_target\": \"10_validations_plus_infrastructure\""
echo "  },"

# Infrastructure timing
echo "  \"infrastructure_metrics\": {"
echo "    \"docker_daemon\": {"
START=$(date +%s%3N)
docker info > /dev/null 2>&1
END=$(date +%s%3N)
echo "      \"check_time_ms\": $((END - START)),"
echo "      \"status\": \"healthy\""
echo "    },"

echo "    \"service_startup\": {"
CONTAINERS=$(docker compose ps --format json 2>/dev/null | jq -r '.Service' | wc -l)
echo "      \"running_containers\": $CONTAINERS,"
echo "      \"services\": ["
docker compose ps --format json 2>/dev/null | jq -c '{name: .Service, status: .Status}' | sed 's/^/        /' | sed '$ ! s/$/,/'
echo "      ]"
echo "    },"

# Neo4j query timing
echo "    \"neo4j_performance\": {"
NEO4J_SAMPLES=()
for i in {1..5}; do
  START=$(date +%s%3N)
  docker compose exec -T neo4j cypher-shell -u neo4j -p "${NEO4J_PASSWORD:-neo4jpass123}" \
    "MATCH (r:Rule {id:'R0'}) RETURN r.id, r.requires_review_for_irreversible, r.priority LIMIT 1" > /dev/null 2>&1
  END=$(date +%s%3N)
  NEO4J_SAMPLES+=($((END - START)))
done
echo "      \"query_samples_ms\": [${NEO4J_SAMPLES[*]}],"
IFS=$'\n' SORTED=($(sort -n <<<"${NEO4J_SAMPLES[*]}"))
echo "      \"min_ms\": ${SORTED[0]},"
echo "      \"median_ms\": ${SORTED[2]},"
echo "      \"max_ms\": ${SORTED[4]}"
echo "    },"

# PostgreSQL timing
echo "    \"postgresql_performance\": {"
PG_SAMPLES=()
for i in {1..5}; do
  START=$(date +%s%3N)
  docker compose exec -T postgres psql -U darf_user -d darf -c "SELECT 1" > /dev/null 2>&1
  END=$(date +%s%3N)
  PG_SAMPLES+=($((END - START)))
done
echo "      \"query_samples_ms\": [${PG_SAMPLES[*]}],"
IFS=$'\n' SORTED_PG=($(sort -n <<<"${PG_SAMPLES[*]}"))
echo "      \"min_ms\": ${SORTED_PG[0]},"
echo "      \"median_ms\": ${SORTED_PG[2]},"
echo "      \"max_ms\": ${SORTED_PG[4]}"
echo "    }"
echo "  },"

# Full validation runs
echo "  \"validation_runs\": ["
for i in {1..10}; do
  ./scripts/core/validate.sh > /dev/null 2>&1
  LATEST=$(ls -t var/receipts/open-darf/validation_*.json | head -1)
  cat "$LATEST" | sed 's/^/    /'
  if [ $i -lt 10 ]; then echo "    ,"; fi
done
echo "  ],"

# System resources
echo "  \"system_resources\": {"
echo "    \"cpu_cores\": $(nproc),"
echo "    \"ram_total_gb\": \"$(free -g | awk '/^Mem:/{print $2}')\","
echo "    \"ram_available_gb\": \"$(free -g | awk '/^Mem:/{print $7}')\","
echo "    \"docker_version\": \"$(docker --version | awk '{print $3}' | tr -d ',')\","
echo "    \"disk_usage_mb\": {"
echo "      \"receipts_dir\": $(du -sm var/receipts/open-darf/ | awk '{print $1}'),"
echo "      \"total_repo\": $(du -sm . | awk '{print $1}')"
echo "    }"
echo "  }"

echo "}" | tee "$RESULTS_FILE"

echo ""
echo "=== Comprehensive metrics saved to: $RESULTS_FILE ==="
