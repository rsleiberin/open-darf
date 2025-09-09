# Architect Handoff — Phase 7H Closeout → Phase 8 Entry

## TL;DR
- **Closed-repo E2E lifecycle** is implemented and accepted (ingest → dedup → surgical removal → targeted resynth → re-eval) with schema-validated receipts and **compliance = 1.0**.
- **Full-suite receipts** exist for SciERC (~0 docs) and BioRED (~0 docs), summarized in `docs/phase7h/FULL_SUITE_SUMMARY.md`.
- **Do not merge to `main` yet.** User directive: **before any open-source packaging**, optimize academic benchmarks; DARF must compete on **every AI frontier** (accuracy, governance, performance, auditability).

## What’s Done (Phase 7H)
- End-to-end lifecycle with receipts for SciERC/BioRED.
- Lineage integrity proven: surgical removals do **not** leave dangling refs; targeted resynthesis scopes correctly.
- Performance within budgets (ingest/dedup/resynth sub-500ms batch timings, compliance overhead ~microseconds).
- Documentation: `STATUS.md`, `RECEIPTS_INDEX.md`, `FULL_SUITE_SUMMARY.md`, and packaged receipts (.zip) under `docs/phase7h/`.

## Gaps vs. Benchmark Goals
- Current re-eval uses **identity evaluator** → F1=1.0 is plumbing validation, **not** model accuracy.
- Phase 7G heuristic baseline on SciERC dev sits at **~0.34 F1_micro**, below targets.
- BioRED loaders: fix normalization to avoid over-aggressive dedup and to preserve relation annotations.

## Phase 8 Objectives (Must-Have before open-source)
1. **Academic Benchmarking:** integrate **PURE** and **PL-Marker**; produce receipts for SciERC (dev/test) and BioRED (full). Targets:
   - SciERC **F1_micro ≥ 0.50**
   - BioRED **entity ≥ 0.90**, **relation ≥ 0.65**
2. **Dataset-Aware Loaders:** stable IDs (PMID + section/offset), relation joins for BioRED official; robust SciERC split handling.
3. **CI Gates Update:** enforce both governance and benchmark thresholds; publish scoreboards in `docs/scoreboards/`.
4. **Positioning:** document DARF's differentiation vs. closed LLMs (ChatGPT/Claude): constitutional receipts, revocation, provenance — **plus** competitive accuracy.

## Branch & State
- Progress saved on **`feat/phase7h-e2e-receipts-acceptance`** (closed repo). Packaged receipts included under `docs/phase7h/*.zip`.
- No changes to `main`. Open PR when Phase 8 benchmarks are recorded.

