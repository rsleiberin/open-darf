Phase 6C technical recovery — receipts and publication pack.

Branch: phase6c-results-20250830-211158
UTC: 20250830-211912

Highlights:
- Environment and model cache validated (Torch CUDA, SciBERT/BioBERT).
- Bench harnesses executed for SciERC and BioRED; receipts, gates, comparisons emitted.
- Archive and provenance generated.

Notes:
- Metrics are baseline zeros pending official dataset fetch; do not treat as final.
- Data and model caches ignored; repo hygiene preserved.

Review checklist:
- [ ] Open docs/implementation/phase6c_results.md
- [ ] Inspect var/reports/phase6c/prov_export.json
- [ ] Confirm validator logs and gates.json
- [ ] Sanity-check receipts paths in accuracy_digest.json

## Agent Context System — Updated (Phase 6C)

This PR includes the updated **agent context system** (operational doctrine for implementation agents). It is now committed to `docs/agent/*` and used across this branch.

**What’s included (high-level):**
- Tri-state constitutional decisions (**ALLOW | DENY | INDETERMINATE**) with **DENY precedence** and fail-closed defaults.
- Progress bar & checklist protocol (status tokens, grouping, update-only rule).
- Command execution standard via **bash heredocs** (idempotent, single-step, explicit success/failure).
- Multi-agent **handoff** protocol (handoff docs, receipts, deviations, perf notes).
- Quality & performance gates (pre-commit, tests, receipts; p95 targets captured in docs).
- Provenance expectations (W3C PROV-O framing), error handling & **resume** script pattern.
- Dynamic context file map (roadmap, handoff, checklist, tech stack).
- Quick command reference for day-to-day ops.

**Files added/updated under `docs/agent/` in this PR:**
 - A	docs/agent/AGENT_OPERATING_CORE.md
 - M	docs/agent/AGENT_OPERATING_GUIDE.md
 - A	docs/agent/current_phase.md
 - A	docs/agent/darf_identity.md
 - A	docs/agent/github_operations.md
 - A	docs/agent/modular_context_framework.md
 - A	docs/agent/performance_targets.md
 - A	docs/agent/tech_stack.yaml

_Commit:_ `a969b06` — docs(biored): note source URL rot; apply EOF/whitespace normalizations
_Branch:_ `docs/agent-knowledge-update`

> Rationale: Publishing the agent context system alongside Phase 6C ensures reviewers and future agents have the same operating constraints and runbooks used to produce the current receipts and gates.

**SciERC official-dict baseline (test):** F1 = 0.09919877909194963 (ref: `var/receipts/phase6c/infer/scierc_official/20250901-184455/metrics_test.json`).

Validation receipts refreshed; SciERC trained F1=0.307 (numbers-to-beat), official-dict baseline F1=0.099 — uplift documented in gates.

Validation receipts & gates re-emitted after fixing summarizer inputs (BioRED shims).

> Metrics pipeline now runs in **strict mode** (no handoff fallbacks).
> If relation metrics are absent in baked receipts, we set them to 0.0 with explicit provenance flags.

### Emitter update
- Enhanced `scripts/emit_perf_and_constitution.py` to pass through dataset sections from `validation/metrics.json` (non-invasive).
- Metrics remain **strict-mode**; provenance preserved in validation artifacts.

### CI Gate
- Added `scripts/ci_verify_gates.py` to enforce presence and non-regression of dataset metrics in `gates.json`.
- Current thresholds (numbers-to-beat): SciERC entity F1 **0.3070**, BioRED entity F1 **0.6310**.

### CI Gates Workflow
- Adds `.github/workflows/ci-gates.yml` which:
  1) Emits `gates.json` from validation artifacts (strict mode),
  2) Runs `scripts/ci_verify_gates.py` to enforce thresholds,
  3) Prints a human-friendly scoreboard for reviewers.
