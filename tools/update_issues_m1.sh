#!/usr/bin/env bash
set -Ee -o pipefail
trap 'echo "[ERR] line:$LINENO status:$?" >&2' ERR

# --- Guards -------------------------------------------------------------------
command -v gh >/dev/null || { echo "[FATAL] gh CLI not found" >&2; exit 1; }
gh auth status >/dev/null || { echo "[FATAL] gh not authenticated" >&2; exit 1; }
git rev-parse --is-inside-work-tree >/dev/null 2>&1 || { echo "[FATAL] not inside a git repo" >&2; exit 1; }

REMOTE="$(git config --get remote.origin.url || true)"
if [[ -z "$REMOTE" ]]; then
  echo "[WARN] No git remote set; gh will use current directory context." >&2
else
  echo "[INFO] Remote: $REMOTE" >&2
fi

DATE_UTC="$(date -u +'%Y-%m-%d %H:%M:%S UTC')"

# --- Labels -------------------------------------------------------------------
ensure_label () {
  local name="$1" color="$2" desc="$3"
  if ! gh label list --limit 500 --json name | jq -r '.[].name' | grep -Fxq "$name"; then
    gh label create "$name" --color "$color" --description "$desc" >/dev/null
    echo "[OK] Created label: $name"
  else
    echo "[SKIP] Label exists: $name"
  fi
}

ensure_label "Milestone: M1" "0e8a16" "Milestone 1 (MVP Core)"
ensure_label "spec-locked"   "5319e7" "Spec locked — ready for implementation"

# --- Issue sets ---------------------------------------------------------------
# M1 issues: label with Milestone: M1; most also get spec-locked
M1_ISSUES=(153 166 167 168 169 170 171 172 173 174 175 176 182 183)
SPEC_LOCK_ISSUES=(166 167 168 169 170 171 172 173 174 175 176 182 183)
# Additional non-M1 that get spec comments only (no M1 label by default)
EXTRA_SPEC_ISSUES=(177 178 179 180 181)

# --- Helpers ------------------------------------------------------------------
add_labels () {
  local num="$1"
  local add_m1="$2"
  local add_spec="$3"
  local args=()
  [[ "$add_m1" == "1" ]] && args+=(--add-label "Milestone: M1")
  [[ "$add_spec" == "1" ]] && args+=(--add-label "spec-locked")
  if ((${#args[@]})); then
    gh issue edit "$num" "${args[@]}" >/dev/null
    echo "[OK] Labels applied to #$num: ${args[*]//--add-label /}"
  else
    echo "[SKIP] No labels to apply for #$num"
  fi
}

post_comment () {
  local num="$1"
  local tmp
  tmp="$(mktemp)"
  build_comment_body "$num" > "$tmp"
  if [[ -s "$tmp" ]]; then
    gh issue comment "$num" --body-file "$tmp" >/dev/null
    echo "[OK] Comment posted to #$num"
  else
    echo "[SKIP] No comment body for #$num"
  fi
  rm -f "$tmp"
}

# Compose per-issue comment bodies (minimal, precise "Spec Lock — M1" updates)
build_comment_body () {
  local num="$1"
  case "$num" in
    166) cat <<EOF
**Spec Lock — M1 (${DATE_UTC}) — W3C DID + Hierarchical Key Mgmt**

- Derivation path: \`m/44'/0'/account'/purpose'/index\`
- Purpose codes: \`0=device\`, \`1=sync\`, \`2=const-enc\`
- Acceptance: test vectors per purpose; derivation path appears in receipts
EOF
    ;;
    167) cat <<EOF
**Spec Lock — M1 (${DATE_UTC}) — Hardware-backed Keys**

- Keys never leave TPM/SE/TEE; attestation blob stored
- Policy: L3 requires attestation; L0–L2 permitted with risk note
- Acceptance: attested→L3 allowed; fallback→L3 denied
EOF
    ;;
    168) cat <<EOF
**Spec Lock — M1 (${DATE_UTC}) — Multi-device CRDT Sync**

- Prefs: LWW-Element-Set + dotted version vectors; Docs: RGA
- Targets: sub-second active convergence; 30-day offline rejoin
- Acceptance: 10-device merge p95 < 1s; offline rejoin preserves order
EOF
    ;;
    169) cat <<EOF
**Spec Lock — M1 (${DATE_UTC}) — HVC Liveness (ISO/IEC 30107-3; FIDO)**

- ZK stack: BBS+ (selective disclosure) + Plonk (general proof)
- VC fields: uniqueness_nullifier, jurisdiction_proof, liveness_ts, eligibility (+cmp/membership/eq)
- Acceptance: on-device PAD; server verifies proofs only (no biometric egress)
EOF
    ;;
    170) cat <<EOF
**Spec Lock — M1 (${DATE_UTC}) — DB & APIs**

- Contracts explicit: REST, GraphQL, WS (revocation/session topics)
- ACID on identity ops; adapters for Postgres/Neo4j/Qdrant
- Acceptance: contract tests; clean migrations apply
EOF
    ;;
    171) cat <<EOF
**Spec Lock — M1 (${DATE_UTC}) — Observability & SLOs**

- SLOs: ID ≤ 1s; audit p95 ≤ 10s; revoke p95 ≤ 2s; compliance < 500ms; consensus ≤ 30s
- Acceptance: probes + Grafana panels + SLO burn alert
EOF
    ;;
    172) cat <<EOF
**Spec Lock — M1 (${DATE_UTC}) — Capabilities v0**

- TTLs: L0=30m; L1=4h; L2=12h; L3=2h
- Receipts include revocation pointer
- Acceptance: revoke p95 ≤ 1.5s, p99 ≤ 3s across ≥ 3 regions
EOF
    ;;
    173) cat <<EOF
**Spec Lock — M1 (${DATE_UTC}) — Revocation Push + Offline Proofs**

- O(log n) push; offline delta proofs retained 72h; audit trail 30d
- Acceptance: offline reconnect enforces revocation via delta proof
EOF
    ;;
    174) cat <<EOF
**Spec Lock — M1 (${DATE_UTC}) — BFT Sessions**

- Vector clocks for causal ordering; quorum safety target 99.95%
- Acceptance: fault injection shows session consistency under partition
EOF
    ;;
    175) cat <<EOF
**Spec Lock — M1 (${DATE_UTC}) — Principle Extraction → Formal Specs**

- Map NLP rules to Transform invariants; ≥ 95% spot-check fidelity
- Acceptance: rule coverage report with exceptions list
EOF
    ;;
    176) cat <<EOF
**Spec Lock — M1 (${DATE_UTC}) — Runtime Checks (Neuro-symbolic)**

- Budgets/thresholds: < 500ms; VIF proxy ≥ 0.85; similarity ≥ 0.92; 7d adaptive window
- Acceptance: allow/deny with rationale; drift alerts emitted
EOF
    ;;
    177) cat <<EOF
**Spec Lock (${DATE_UTC}) — Democratic Engines**

- Quorum intersection ≥ f+1 overlap; safety target 99.95%
- Liquid democracy + quadratic voting with cryptographic commitments
- Acceptance: sim verifies intersection; ballots/delegation produce commitments
EOF
    ;;
    178) cat <<EOF
**Spec Lock (${DATE_UTC}) — Democratic Health Metrics**

- Include participation, satisfaction, minority protection; standard decisions ≤ 30s
- Acceptance: dashboards + alerts wired to decision times
EOF
    ;;
    179) cat <<EOF
**Spec Lock (${DATE_UTC}) — Guardians (K-of-N, DKG/MPC)**

- 36h guardian change delay; mandatory periodic rotation
- Acceptance: emergency rotation drill with receipts
EOF
    ;;
    180) cat <<EOF
**Spec Lock (${DATE_UTC}) — Succession & Tombstone**

- 180d grace with monthly confirmations; 3-of-5 multi-channel inactivity threshold
- Acceptance: simulated succession with full audit + heir MFA
EOF
    ;;
    181) cat <<EOF
**Spec Lock (${DATE_UTC}) — Humanitarian Safe Mode**

- Triggers: verified NGO attestations + geo crisis correlation + network restriction analysis
- Acceptance: reduced auth + extended offline; core rights preserved
EOF
    ;;
    182) cat <<EOF
**Spec Lock — M1 (${DATE_UTC}) — TLA+ Harness in CI (small-model)**

- Safety: quorum intersection; capability revocation propagation; receipt invariants
- Liveness: consensus termination
- Acceptance: TLC small-model green; CI uploads counterexample fixtures
EOF
    ;;
    183) cat <<EOF
**Spec Lock — M1 (${DATE_UTC}) — ProVerif + PQC Pilot (behind flag)**

- Priorities: HVC attestation; revocation chain; guardian recovery
- PQC: ML-KEM-768, ML-DSA-65, SLH-DSA-128s + benches
- Acceptance: models compile; PQC path reports size/latency deltas
EOF
    ;;
    153) cat <<EOF
**M1 Gate (${DATE_UTC}) — pre-commit InvalidConfigError**

- Goal: \`pre-commit run -a\` passes locally; CI green
- Acceptance: YAML structure audited; hooks fixed; validator hardened
EOF
    ;;
    *) : ;;
  esac
}

# --- Apply updates ------------------------------------------------------------
# 1) Comments + labels for M1 issues
for n in "${M1_ISSUES[@]}"; do
  post_comment "$n"
  add_labels "$n" 1 1
done

# 2) Comments + spec-locked for extra governance/recovery issues (no M1 label)
for n in "${EXTRA_SPEC_ISSUES[@]}"; do
  post_comment "$n"
  add_labels "$n" 0 1
done

# 3) Add only M1 label to #153 if not already applied (comment already posted above)
add_labels "153" 1 0

echo
echo "[DONE] Spec Lock comments posted and labels applied."
echo "       Timestamp: ${DATE_UTC}"
