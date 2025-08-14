#!/usr/bin/env bash
set -Ee -o pipefail
trap 'echo "[ERR] line:$LINENO status:$?" >&2' ERR

# --- Guards -------------------------------------------------------------------
command -v gh >/dev/null || { echo "[FATAL] gh CLI not found" >&2; exit 1; }
command -v jq >/dev/null || { echo "[FATAL] jq not found" >&2; exit 1; }
gh auth status >/dev/null || { echo "[FATAL] gh not authenticated" >&2; exit 1; }
git rev-parse --is-inside-work-tree >/dev/null 2>&1 || { echo "[FATAL] not inside a git repo" >&2; exit 1; }

DATE_UTC="$(date -u +'%Y-%m-%d %H:%M:%S UTC')"

# Derive owner/repo from remote (fallback to gh)
REMOTE="$(git config --get remote.origin.url || true)"
case "$REMOTE" in
  https://github.com/*/*.git) OWNER="$(basename "$(dirname "$REMOTE")")"; REPO="$(basename -s .git "$REMOTE")" ;;
  git@github.com:*.git) OWNER="$(echo "$REMOTE" | sed -E 's|git@github.com:([^/]+)/([^/]+)\.git|\1|')"; REPO="$(echo "$REMOTE" | sed -E 's|git@github.com:([^/]+)/([^/]+)\.git|\2|')" ;;
  *) OWNER_REPO="$(gh repo view --json nameWithOwner -q .nameWithOwner)"; OWNER="${OWNER_REPO%/*}"; REPO="${OWNER_REPO#*/}";;
esac
echo "[INFO] Repo: $OWNER/$REPO"

api() { gh api "$@" -H "Accept: application/vnd.github+json"; }

# --- Labels (CLI; avoids REST form pitfalls) ----------------------------------
ensure_label () {
  local name="$1" color="$2" desc="$3"
  if ! gh label list --limit 500 --json name | jq -r '.[].name' | grep -Fxq "$name"; then
    gh label create "$name" --color "$color" --description "$desc" >/dev/null
    echo "[OK] Created label: $name"
  else
    echo "[SKIP] Label exists: $name"
  fi
}
ensure_label "Stream" "0366d6" "Top-level implementation stream"
ensure_label "spec-locked" "5319e7" "Spec locked — ready for implementation"
ensure_label "Roadmap:2025-2026" "b60205" "Items tied to the 2025–2026 roadmap"

# --- Milestones (Phase 3–5) via REST (this part worked earlier) ---------------
upsert_milestone () {
  local title="$1" due_on="$2" desc="$3"
  local ms; ms="$(api "/repos/$OWNER/$REPO/milestones?state=all&per_page=100")"
  local num; num="$(echo "$ms" | jq -r --arg t "$title" '.[] | select(.title==$t) | .number' || true)"
  if [[ -n "$num" ]]; then
    api -X PATCH "/repos/$OWNER/$REPO/milestones/$num" -f description="$desc" -f due_on="$due_on" >/dev/null
    echo "$num"
  else
    api -X POST "/repos/$OWNER/$REPO/milestones" -f title="$title" -f description="$desc" -f due_on="$due_on" | jq -r '.number'
  fi
}

MS3_TITLE="Phase 3 — Constitutional Implementation (Q4 2025–Q1 2026)"
MS4_TITLE="Phase 4 — Integration & Verification (Q1 2026–Q2 2026)"
MS5_TITLE="Phase 5 — Production & Optimization (Q2 2026–Q4 2026)"
MS3_NUM="$(upsert_milestone "$MS3_TITLE" "2026-03-31T23:59:59Z" "Constraint engine + AP-PBFT + initial transform. Targets: 170ms constraint checks, 500ms consensus, 100% preservation.")"
MS4_NUM="$(upsert_milestone "$MS4_TITLE" "2026-06-30T23:59:59Z" "Formal verification integration (TLA+/TLAPS), PQC pilot/migration, CI artifacts.")"
MS5_NUM="$(upsert_milestone "$MS5_TITLE" "2026-12-31T23:59:59Z" "Prod rollout, scaling & optimization; governance scaling & audits.")"
echo "[OK] Milestones => P3:#$MS3_NUM P4:#$MS4_NUM P5:#$MS5_NUM"

# --- Helpers ------------------------------------------------------------------
issue_exists_by_title () {
  local title="$1"
  gh issue list -L 200 --json number,title | jq -r --arg t "$title" '.[] | select(.title==$t) | .number' || true
}

ensure_labels_and_milestone () {
  local num="$1" ms_title="$2"
  shift 2
  for L in "$@"; do gh issue edit "$num" --add-label "$L" >/dev/null || true; done
  gh issue edit "$num" --milestone "$ms_title" >/dev/null || true
}

create_issue_cli () {
  local title="$1" body_file="$2" milestone_title="$3"; shift 3
  local labels=( "$@" )
  # Build repeated -l args
  local largs=()
  for L in "${labels[@]}"; do largs+=( -l "$L" ); end="${L}"; done
  # Create; parse URL -> number
  local out
  if ! out="$(gh issue create -t "$title" -F "$body_file" -m "$milestone_title" "${largs[@]}")"; then
    echo "[FATAL] gh issue create failed for: $title" >&2
    return 1
  fi
  echo "$out" | grep -Eo '[0-9]+$' || true
}

# --- Stream issue bodies (written to temp files) ------------------------------
mk_body_file () {
  local varname="$1"
  local tmp; tmp="$(mktemp)"
  case "$varname" in
    S1) cat >"$tmp" <<'EOF'
**Objective**: Hierarchical constitutional constraint validation with mathematical preservation during anchor transforms.

**Acceptance**
- Validate ≥1,000,000 constraint relationships with Neo4j query latency ≤ **170 ms**.
- **100%** constitutional constraint preservation across all transform scenarios.
- Handle hierarchical depth up to **10** levels without perf degradation.
- Constraint conflict detect+resolve ≤ **100 ms**.

**Deliverables**
- Neo4j schema extensions (constraint nodes/rels); validation API; perf benches; proofs & tests.

**Roadmap v2025–2026** (auto-upsert)
EOF
    ;;
    S2) cat >"$tmp" <<'EOF'
**Objective**: Democratic preference aggregation with BFT guarantees.

**Acceptance**
- Safety with up to **33%** malicious participants.
- Constitutional decision ops complete ≤ **500 ms**.
- Support **1000+** concurrent decisions.
- Maintain AP-PBFT threshold \(n > 2x_s(G) + x_r(G) + 3t\); VRF + incentive hooks.

**Deliverables**
- AP-PBFT impl + adversarial harness; identity gating; legitimacy metrics.

**Roadmap v2025–2026** (auto-upsert)
EOF
    ;;
    S3) cat >"$tmp" <<'EOF'
**Objective**: Transform content-addressable anchors into ANRs/ADRs with constitutional preservation.

**Acceptance**
- Transform time ≤ **100 ms** per item.
- Semantic compression ≥ **6%** while maintaining ≥ **99%** similarity on constitutional content.
- **100%** constitutional constraint preservation verified by Stream 1.

**Integration**
- MinIO (artifacts), Qdrant (similarity), Neo4j (constraint links).

**Roadmap v2025–2026** (auto-upsert)
EOF
    ;;
    S4) cat >"$tmp" <<'EOF'
**Objective**: Mechanically-checked safety/liveness proofs for constraint + consensus.

**Acceptance**
- TLAPS proofs for constitutional safety invariants; CI-bounded verification.
- Model checking covers concurrent decisions & preservation scenarios.
- Spec–test trace roundtrip wired in CI artifacts.

**Roadmap v2025–2026** (auto-upsert)
EOF
    ;;
    S5) cat >"$tmp" <<'EOF'
**Objective**: Quantum-safe verification using CRYSTALS-Kyber (KEM) & CRYSTALS-Dilithium (DSA).

**Acceptance**
- FIPS 203–205 compliance validated.
- Performance overhead ≤ **5×** for constitutional verification ops.
- Hybrid migration path; long-term security ≥ **50+ years**.

**Note**
- Keep naming parity with ML-KEM/ML-DSA in #183; benches behind feature flag.

**Roadmap v2025–2026** (auto-upsert)
EOF
    ;;
  esac
  echo "$tmp"
}

# --- Ensure 5 Stream umbrella issues -----------------------------------------
declare -A STREAMS=(
  ["Stream 1 — Constitutional Constraint Satisfaction Engine"]="S1|$MS3_TITLE"
  ["Stream 2 — AP-PBFT Byzantine Preference Aggregation"]="S2|$MS3_TITLE"
  ["Stream 3 — Anchor Transformation Pipeline (Anchor → ANR/ADR)"]="S3|$MS4_TITLE"
  ["Stream 4 — Formal Verification Integration (TLA+/TLAPS in CI)"]="S4|$MS4_TITLE"
  ["Stream 5 — Post-Quantum Constitutional Security (FIPS 203–205)"]="S5|$MS5_TITLE"
)

for TITLE in "${!STREAMS[@]}"; do
  KEY="${STREAMS[$TITLE]%%|*}"; MS_T="${STREAMS[$TITLE]##*|}"
  NUM="$(issue_exists_by_title "$TITLE")"
  if [[ -n "$NUM" ]]; then
    ensure_labels_and_milestone "$NUM" "$MS_T" "Stream" "Roadmap:2025-2026" "spec-locked"
    echo "[OK] Ensured labels/milestone on #$NUM ($TITLE)"
  else
    BODY_FILE="$(mk_body_file "$KEY")"
    NEW_NUM="$(create_issue_cli "$TITLE" "$BODY_FILE" "$MS_T" "Stream" "Roadmap:2025-2026" "spec-locked")"
    rm -f "$BODY_FILE"
    if [[ -n "$NEW_NUM" ]]; then
      echo "[OK] Created $TITLE as #$NEW_NUM"
    else
      echo "[WARN] Could not parse issue number for: $TITLE (creation likely succeeded; check repo)"
    fi
  fi
done

# --- Roadmap addenda to existing issues (dedup w/ marker) ---------------------
post_addendum () {
  local num="$1" body="$2"
  # Dedup: skip if marker already present in recent comments
  if gh issue view "$num" --comments --json comments -q '.comments[].body' 2>/dev/null | grep -Fq "[Roadmap 2025–2026]"; then
    echo "[SKIP] Addendum already present on #$num"
  else
    gh issue comment "$num" --body "$body" >/dev/null
    echo "[OK] Addendum posted to #$num"
  fi
}

A171=$'[Roadmap 2025–2026] SLO precision ('"$DATE_UTC"$')\n- Constraint validation SLO: **≤170 ms** (Neo4j constraint graph queries).\n- Consensus operation SLO: **≤500 ms** (AP-PBFT preference ops).\n- Transform SLO: **≤100 ms** per anchor → ANR/ADR.'
A174=$'[Roadmap 2025–2026] Consensus targets ('"$DATE_UTC"$')\n- Safety with up to **33%** malicious; ops **≤500 ms**; support **1000+** concurrent decisions.\n- Keep AP-PBFT threshold \(n > 2x_s(G) + x_r(G) + 3t\).'
A175=$'[Roadmap 2025–2026] Constraint engine coupling ('"$DATE_UTC"$')\n- Require **100%** constitutional preservation during transforms; depth ≤10; conflict resolve ≤100 ms.\n- Expose validation API for Stream 3 checks.'
A176=$'[Roadmap 2025–2026] Runtime checks budget ('"$DATE_UTC"$')\n- When constraint engine engaged, per-call rule eval **≤170 ms**; overall gate **< 500 ms**.'
A170=$'[Roadmap 2025–2026] Schema integration ('"$DATE_UTC"$')\n- Add Neo4j constraint nodes/rels; Qdrant similarity for constitutional content; MinIO artifacts for transforms.'
A183=$'[Roadmap 2025–2026] PQC targets ('"$DATE_UTC"$')\n- Use CRYSTALS-Kyber/Dilithium (FIPS 203–205) alongside ML-KEM/ML-DSA naming in #183.\n- Bench overhead ≤ **5×**; hybrid migration path retained.'

post_addendum 171 "$A171"
post_addendum 174 "$A174"
post_addendum 175 "$A175"
post_addendum 176 "$A176"
post_addendum 170 "$A170"
post_addendum 183 "$A183"

echo "[DONE] Roadmap milestones ensured, Stream issues ensured, and addenda deduped."
