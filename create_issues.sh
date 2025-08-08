#!/usr/bin/env bash
set -euo pipefail
trap 'echo "ERR: ${BASH_SOURCE[0]}:${LINENO} – last cmd: ${BASH_COMMAND}" >&2' ERR

REPO="${1:-$(gh repo view --json nameWithOwner -q .nameWithOwner 2>/dev/null || true)}"
if [[ -z "${REPO}" ]]; then
  echo "ERR: No repo detected. Pass owner/repo explicitly, e.g. ./create_issues.sh rsleiberin/darf-source" >&2
  exit 1
fi

command -v gh >/dev/null || { echo "ERR: gh CLI not found"; exit 1; }
command -v jq >/dev/null || { echo "ERR: jq not found"; exit 1; }
gh auth status -h github.com >/dev/null || { echo "ERR: gh not authenticated"; exit 1; }

echo "Target repo: ${REPO}"

MILESTONES_JSON="$(cat <<'JSON'
[
  {"title":"Phase 1","description":"Foundations & Provider abstraction, CI/CD"},
  {"title":"Phase 2","description":"Memory, Privacy, EoL, HTN/BDI core"},
  {"title":"Phase 3","description":"Post-mortem, trading infra, monitoring"},
  {"title":"Phase 4","description":"Security extras, research & future work"}
]
JSON
)"

# Create (or confirm) a milestone by title; return its *title* (we'll pass titles to gh)
ensure_milestone_title() {
  local title="$1" desc="$2"
  # Try to find it first
  if gh api -X GET "repos/${REPO}/milestones" --paginate --jq ".[]|select(.title==\"${title}\")|.title" | grep -Fxq "$title"; then
    printf "%s" "$title"; return 0
  fi
  # Try create; if 422 (already exists by race), ignore and re-fetch
  if ! gh api -X POST "repos/${REPO}/milestones" -f title="$title" -f description="$desc" >/dev/null 2>&1; then
    :
  fi
  # Re-check
  if gh api -X GET "repos/${REPO}/milestones" --paginate --jq ".[]|select(.title==\"${title}\")|.title" | grep -Fxq "$title"; then
    printf "%s" "$title"; return 0
  fi
  echo "ERR: failed to ensure milestone '$title'" >&2
  exit 1
}

declare -A LABEL_COLORS=(
  ["type:feature"]="0e8a16" ["type:docs"]="1d76db" ["type:research"]="5319e7"
  ["enhancement"]="a2eeef" ["type:enhancement"]="a2eeef"
  ["area:backend"]="0052cc" ["area:frontend"]="fbca04" ["area:infra"]="0b4f6c" ["area:devops"]="5319e7" ["area:security"]="b60205" ["area:docs"]="c2e0c6"
  ["priority:high"]="b60205" ["priority:medium"]="d93f0b" ["priority:low"]="0e8a16"
)

ensure_label() {
  local name="$1" color="${LABEL_COLORS[$1]:-ededed}"
  if ! gh label list --repo "${REPO}" --limit 500 --json name | jq -er --arg n "$name" '.[]|select(.name==$n)' >/dev/null 2>&1; then
    gh label create "$name" --color "$color" --repo "${REPO}" --force >/dev/null
  fi
}

ISSUES="$(cat <<'JSON'
[
  {"title":"Implement Provider Abstraction Layer","milestone":"Phase 1","labels":["type:feature","area:backend","priority:high"],"body":"Create swappable backend interfaces for compute, storage, and attestation.\n- Define abstract base classes\n- Implement local/cloud adapters\n- Add configuration management\n- Write integration tests"},
  {"title":"Build Memory Tile System","milestone":"Phase 2","labels":["type:feature","area:backend","priority:high"],"body":"Implement neuroscience-based 72-hour TTL memory management.\n- Create MemoryTile class with timestamp/summary/hash\n- Automatic summarization after TTL\n- Byzantine consensus for multi-device\n- Proof-of-forgetting logging"},
  {"title":"Create Privacy Bridge MVP","milestone":"Phase 2","labels":["type:feature","area:backend","priority:high"],"body":"Build zero-knowledge proof verification for compliance.\n- Mock credential wallet\n- Selective disclosure proofs\n- ADR policy verification engine\n- Attestation-only logging"},
  {"title":"Implement End-of-Log Pipeline","milestone":"Phase 2","labels":["type:feature","area:backend","priority:high"],"body":"Secure pipeline for processing completed conversations.\n- Detect END_OF_LOG markers\n- PII scrubbing\n- Summary generation\n- Remote deletion APIs"},
  {"title":"Build Heartbeat Oracle System","milestone":"Phase 3","labels":["type:feature","area:backend","priority:medium"],"body":"Prevent orphaned agents after user death.\n- 30-day inactivity detection\n- Multi-party confirmation\n- Tombstone mode\n- Public registry"},
  {"title":"Document Memory Tile Architecture (ADR-GOV-002)","milestone":"Phase 2","labels":["type:docs","area:docs","priority:high"],"body":"Create comprehensive ADR for memory tile system.\n- Neuroscience citations\n- Hash pointer implementation\n- Byzantine consensus protocol\n- Integration examples"},
  {"title":"Document Post-Mortem Governance (ADR-GOV-003)","milestone":"Phase 3","labels":["type:docs","area:docs","priority:medium"],"body":"Specify agent lifecycle after user death.\n- Heartbeat oracle\n- Dead-man switch\n- Heir succession\n- Tombstone behavior"},
  {"title":"Document Privacy Bridge (ADR-GOV-004)","milestone":"Phase 2","labels":["type:docs","area:docs","priority:high"],"body":"Define zero-knowledge compliance verification.\n- Selective disclosure\n- Proof requirements\n- Attestation format\n- System integration"},
  {"title":"Create Provider Abstraction ADR (ADR-TEC-001)","milestone":"Phase 1","labels":["type:docs","area:docs","priority:high"],"body":"Document pluggable backend architecture.\n- Interface specs\n- Implementation reqs\n- Migration strategies\n- Benchmarks"},
  {"title":"Implement HTN Planner","milestone":"Phase 2","labels":["type:feature","area:backend","priority:high"],"body":"Build Hierarchical Task Network for decision decomposition.\n- SHOP2-inspired impl\n- PostgreSQL integration\n- Decomposition algorithms\n- Perf optimization"},
  {"title":"Create BDI Reactive Agent","milestone":"Phase 2","labels":["type:feature","area:backend","priority:high"],"body":"Implement Belief-Desire-Intention triggers.\n- JASON-inspired\n- Event-driven beliefs\n- Intention adoption\n- Dramatiq integration"},
  {"title":"Build Saga Coordinator","milestone":"Phase 3","labels":["type:feature","area:backend","priority:medium"],"body":"Distributed transaction mgmt for crypto ops.\n- Orchestration-based saga\n- Compensation handlers\n- State machine\n- ADR constraint integration"},
  {"title":"Implement Cascade Control","milestone":"Phase 2","labels":["type:feature","area:backend","priority:high"],"body":"Manage ADR trigger cascades with safety limits.\n- Depth-first engine\n- Circuit breakers\n- Backpressure\n- Monitoring & alerts"},
  {"title":"Create Merkle Audit Log","milestone":"Phase 3","labels":["type:feature","area:backend","priority:medium"],"body":"Implement proof-of-forgetting & provenance.\n- Hash trail\n- Deletion proofs\n- Query interface\n- Compliance integration"},
  {"title":"Implement Duress Protection","milestone":"Phase 4","labels":["type:feature","area:security","priority:low"],"body":"Add duress passphrase & emergency procedures.\n- Duress detection\n- Key deletion on duress\n- Dummy UI\n- Alerts"},
  {"title":"Add Shamir's Secret Sharing","milestone":"Phase 4","labels":["type:feature","area:security","priority:low"],"body":"Implement key splitting for inheritance.\n- Generation & splitting\n- Threshold reconstruction\n- Secure distribution\n- Post-mortem integration"},
  {"title":"Create Compliance Dashboard","milestone":"Phase 3","labels":["type:feature","area:frontend","priority:medium"],"body":"Build monitoring for regulatory requirements.\n- GDPR tracking\n- MiCA/FinCEN reporting\n- Audit visualization\n- Export"},
  {"title":"Implement Constitutional Validators","milestone":"Phase 2","labels":["type:feature","area:backend","priority:high"],"body":"Build hard constraint enforcement.\n- Financial limits\n- Privacy rules\n- Prohibited action blocking\n- Human review triggers"},
  {"title":"Setup Time-Series Infrastructure","milestone":"Phase 3","labels":["type:feature","area:infra","priority:medium"],"body":"Deploy QuestDB & TimescaleDB for market data.\n- QuestDB ticks\n- Timescale rollups\n- Retention policies\n- Query optimization"},
  {"title":"Build Pattern Detection Pipeline","milestone":"Phase 4","labels":["type:feature","area:backend","priority:low"],"body":"Implement market microstructure analysis.\n- LOB features\n- HDBSCAN\n- Backtesting\n- Strategy library"},
  {"title":"Create Risk Management Gates","milestone":"Phase 4","labels":["type:feature","area:backend","priority:low"],"body":"Implement ADR-based trading constraints.\n- VaR\n- Kelly criterion\n- Drawdown monitoring\n- Auto-halt"},
  {"title":"Research Legal Informatics Integration","milestone":"Phase 4","labels":["type:research","area:docs","priority:low"],"body":"Investigate formal legal reasoning systems.\n- Deontic logic\n- LegalRuleML\n- Exceptions\n- Precedent encoding"},
  {"title":"Evaluate Stuart Russell Alignment","milestone":"Phase 4","labels":["type:research","area:docs","priority:low"],"body":"Research Human Compatible AI integration.\n- Value alignment\n- Uncertainty\n- Off-switch\n- Reward hacking prevention"},
  {"title":"Design Native Token Economics","milestone":"Phase 4","labels":["type:research","area:docs","priority:low"],"body":"Research tokenomics for governance incentives.\n- Stake commitment\n- Reputation\n- Participation rewards\n- Economic attack prevention"},
  {"title":"Investigate Federated Learning","milestone":"Phase 4","labels":["type:research","area:docs","priority:low"],"body":"Privacy-preserving model updates.\n- Differential privacy\n- Secure aggregation\n- Poisoning prevention\n- Perf implications"},
  {"title":"Create Staging Environment","milestone":"Phase 2","labels":["type:enhancement","area:infra","priority:medium"],"body":"Setup pre-production testing env.\n- Mirror prod\n- Data anonymization\n- Perf testing tools\n- Deployment automation"},
  {"title":"Implement Monitoring Stack","milestone":"Phase 3","labels":["type:enhancement","area:devops","priority:medium"],"body":"Deploy comprehensive monitoring.\n- Prometheus\n- Grafana dashboards\n- Alerts\n- Log aggregation"},
  {"title":"Setup CI/CD Pipeline","milestone":"Phase 1","labels":["type:enhancement","area:devops","priority:high"],"body":"Automate testing & deployment.\n- GitHub Actions\n- Test automation\n- Security scanning\n- Deployment gates"},
  {"title":"Create Backup Strategy","milestone":"Phase 2","labels":["type:enhancement","area:infra","priority:high"],"body":"Implement comprehensive backups.\n- DB backups\n- Key backup procedures\n- DR plan\n- Regular recovery tests"}
]
JSON
)"

# Ensure milestones (by title) and labels
declare -A MOK
while IFS= read -r row; do
  t=$(jq -r .title <<<"$row"); d=$(jq -r .description <<<"$row")
  ensure_milestone_title "$t" "$d" >/dev/null
  MOK["$t"]=1
done < <(jq -c '.[]' <<<"$MILESTONES_JSON")

jq -r '.[]|.labels[]' <<<"$ISSUES" | sort -u | while IFS= read -r L; do
  [[ -n "$L" ]] && ensure_label "$L"
done

# Cache existing titles once
existing_titles="$(gh issue list --repo "${REPO}" --limit 1000 --json title | jq -r '.[].title')"

created=0 skipped=0
while IFS= read -r item; do
  title="$(jq -r .title <<<"$item")"
  body="$(jq -r .body <<<"$item")"
  milestone_title="$(jq -r .milestone <<<"$item")"
  labels_csv="$(jq -r '[.labels[]]|join(",")' <<<"$item")"

  if grep -Fxq "$title" <<<"$existing_titles"; then
    echo "SKIP: $title"; ((skipped++)) || true; continue
  fi

  # Use milestone *title* directly; gh accepts title or number
  gh issue create --repo "${REPO}" \
    --title "$title" \
    --body "$body" \
    --label "$labels_csv" \
    --milestone "$milestone_title" >/dev/null

  echo "CREATED: $title"
  ((created++)) || true
done < <(jq -c '.[]' <<<"$ISSUES")

echo "Done. Created: $created, Skipped: $skipped"
