#!/usr/bin/env bash
set -euo pipefail
REPO="rsleiberin/darf-source"
gh_api(){ gh api "$@"; }

# ---------- fetch existing titles ----------
declare -A EXISTING
while read -r t; do EXISTING["$t"]=1; done < <(gh issue list --repo "$REPO" --state all --json title -q '.[].title')

# ---------- ensure milestones ----------
declare -A PHASE_DESC=(
  ["Phase 0"]="Foundation Day-1"
  ["Phase 1"]="Core Infrastructure (Weeks 1-2)"
  ["Phase 2"]="Core Migration (Months 1-3)"
  ["Phase 3"]="Advanced Intelligence (Months 4-9)"
  ["Phase 4"]="Observability & Ops (Months 10-12)"
)
for p in "${!PHASE_DESC[@]}"; do
  gh_api repos/$REPO/milestones | jq -r '.[].title' | grep -qx "$p" || \
    gh_api repos/$REPO/milestones -X POST -f title="$p" -f description="${PHASE_DESC[$p]}" >/dev/null
done

# ---------- backlog (pipe-delimited to protect bodies) ----------
CSV=$(cat <<'DATA'
Phase|Title|Body|Labels
Phase 0|Fix pyproject.toml parse error|Locate stray char causing TOMLDecodeError so `make lint` passes.|area:infra,type:bug,priority:high,status:discussion
Phase 0|Decide on research artifact|Commit or delete docs/reference/compass_artifact_wf-*.md with rationale.|area:docs,type:docs,priority:medium,status:discussion
Phase 0|PR: db-postgres-standup|Bundle Phase 0 work, push `db-postgres-standup` branch, open PR.|area:infra,type:feature,status:discussion
Phase 1|Bootstrap Turborepo skeleton|Create root turbo.json, pnpm workspaces; `turbo run lint` passes.|area:infra,type:feature,priority:high,status:discussion
Phase 1|Scaffold apps/backend (FastAPI)|Move existing API to apps/backend; `/health` returns 200.|area:backend,type:feature,status:discussion
Phase 1|Add adr-orchestrator Dramatiq worker|Create apps/adr-orchestrator with Dramatiq entrypoint.|area:backend,type:feature,status:discussion
Phase 1|Container orchestration via Quadlet|.container units for orchestrator, Redis, monitor.|area:infra,type:feature,status:discussion
Phase 1|Extend podman-compose for full stack|Add Redis, RabbitMQ, Neo4j, Qdrant, MinIO.|area:infra,type:feature,status:discussion
Phase 2|Package adr-core data models|SQLAlchemy, Neomodel, Qdrant models (ADR, Cascade, Event).|area:backend,type:feature,status:discussion
Phase 2|Alembic baseline migration|Generate initial revision.|area:backend,type:feature,status:discussion
Phase 2|Neo4j & Redis migrations|Add Cypher schema + Lua scripts.|area:backend,type:feature,status:discussion
Phase 2|Redis Lua back-pressure & circuit breaker|Implement scripts + client.|area:backend,type:enhancement,status:discussion
Phase 2|HTN planner + BDI reactor stubs|workflows/htn_planner.py & bdi_reactor.py.|area:chatbot,type:research,status:discussion
Phase 2|Saga coordinator (distributed txn)|Pattern per research saga guidance.|area:backend,type:enhancement,status:discussion
Phase 2|ADR Dramatiq actors|decision_actor.py, ingestion_actor.py, cascade_actor.py.|area:backend,type:feature,status:discussion
Phase 2|LangChain tools & chains|adr_tool.py, decision_chain.py minimal chain.|area:chatbot,type:feature,status:discussion
Phase 2|GraphRAG base retriever|Hybrid Neo4j + Qdrant retriever.|area:chatbot,type:feature,status:discussion
Phase 2|Migrate legacy 25 ADRs|Load ADRs into new stores.|area:backend,type:feature,status:discussion
Phase 2|Docs: architecture & migration plan|Fill docs/architecture/adr_system_design.md.|area:docs,type:docs,status:discussion
Phase 3|Dynamic taxonomy evolution engine|classification/taxonomy.py with drift detection.|area:chatbot,type:feature,status:discussion
Phase 3|MCDA + Dempster-Shafer confidence|confidence/ package.|area:chatbot,type:feature,status:discussion
Phase 3|Constitutional AI validator|validators.py with YAML rules.|area:chatbot,type:feature,status:discussion
Phase 3|GraphRAG temporal enhancement|Faster query engine and chunker.|area:chatbot,type:enhancement,status:discussion
Phase 3|Blockchain Decision Records PoC|BDR schema + smart-contract stub.|area:backend,type:research,status:discussion
Phase 4|Prometheus metrics & Grafana dashboards|Export Dramatiq, Redis, Postgres metrics.|area:devops,type:enhancement,status:discussion
Phase 4|Kubernetes manifests|Translate Quadlet services into K8s YAML.|area:infra,type:feature,status:discussion
Phase 4|End-to-end cascade performance test|Locust/JMeter script <100 ms retrieval.|area:devops,type:enhancement,status:discussion
Phase 4|Compliance audit export pipeline|SHAP/LIME report + CSV export.|area:chatbot,type:feature,status:discussion
DATA
)

# ---------- create issues (skip duplicates) ----------
echo "$CSV" | while IFS='|' read -r phase title body labels; do
  [[ "$phase" == "Phase" ]] && continue
  [[ -n "${EXISTING[$title]:-}" ]] && { echo "• Skipping existing: $title"; continue; }
  IFS=',' read -ra labs <<<"$labels"
  gh issue create --repo "$REPO" --title "$title" --body "$body" \
    $(for l in "${labs[@]}"; do printf -- '--label %s ' "$l"; done) \
    --milestone "$phase" >/dev/null
done

echo "✅  Backlog populated without duplicates."
