# Phase-6C — Relation Extraction Integration Plan
_Commit:_ `a821dfa`  •  _Generated:_ 2025-09-01T23:30:17Z

## 0) Context & Guardrails
- Maintain clean `main`; PR + squash only. No new issues unless instructed.
- Hermetic, receipt-driven CI Gates; do **not** add networked steps.
- **Do not** modify `*.tla` or verification-owned files.
- Current gates track entity F1 for SciERC and BioRED; BioRED relation F1 is recorded (presently ~0) but **not** a failing gate.

## 1) Current Baselines (from gates.json)
- **SciERC** entity F1: 0.30703012912482064
- **BioRED** entity F1: 0.6310494357786541
- **BioRED** relation F1: 0 (visibility only)

## 2) Scope (this phase)
- Integrate relation extraction pipeline for BioRED (and prepare hooks for SciERC relations if applicable).
- Add deterministic emitters to produce relation metrics into receipts without changing gate logic.
- Provide unit tests + receipt tests to ensure reproducibility.
- Wire constitutional checks around relation post-processing (tri-state ALLOW|DENY|INDETERMINATE) without editing TLA sources.

## 3) Proposed Architecture (high level)
- **Inputs:** existing entity predictions + dataset annotations.
- **Model options:** start with lightweight head(s) or rule-based heuristics as placeholder; enable swap-in for learned relation models later.
- **Pipeline stages:**
  1. Candidate pair generation (windowed sentence/paragraph; type constraints).
  2. Feature construction (context span, dependency hints if available, distance).
  3. Scoring/inference (initially deterministic/heuristic to keep receipts hermetic).
  4. Thresholding + label mapping → relations.jsonl per doc.
  5. Metrics computation (precision/recall/F1 by relation type + micro/macro).
  6. Emit receipts: `var/receipts/phase6c/validation/biored_relations_scores.json`.

- **Constitutional hooks:**
  - Pre-emit: validate that each relation references existing entities (provenance integrity).
  - Post-emit: assert invariants (no self-relations unless allowed; type compatibility).
  - Decision wrapper returns ALLOW on invariant pass; otherwise DENY with explanation.

## 4) Files & Paths (planned)
- `scripts/relation_extraction/`
  - `build_candidates.py` — deterministic candidate generation.
  - `score_relations.py` — pluggable scorer interface.
  - `emit_rel_metrics.py` — writes normalized metrics + receipts.
- `tests/relation_extraction/`
  - `test_candidates.py`, `test_metrics.py` — deterministic fixtures.
- Receipts: `var/receipts/phase6c/validation/biored_relations_scores.json`
- Docs: `docs/plans/phase6c/relation_extraction_plan.md` (this), `docs/verification/relations_invariants.md`.

## 5) Test Strategy
- **Unit:** candidate cardinality given fixed tokenization; metrics on fixed toy corpus.
- **Receipt diff:** a stable miniature fixture checked into repo; CI validates presence & non-regression.
- **Performance:** micro-F1 computed offline; CI consumes receipts only.

## 6) Rollout & CI
- New receipts are uploaded as artifacts; **no gate promotion** in Phase-6C.
- Later (Phase-6D): consider promoting BioRED relation micro-F1 with a conservative baseline.

## 7) Risks & Mitigations
- **Tokenizer/segmentation drift** → lock versions in dev, but CI remains hermetic via receipts.
- **Label mismatch** → strict schema validation; fail-fast in emit step.
- **Heuristic bias** → document limitations; keep pluggable head to swap a learned model later.

## 8) Acceptance
- Receipts present + verified.
- Docs & tests merged via squash; no CI gate regressions.
