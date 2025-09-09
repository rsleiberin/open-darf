# Phase 8 — Benchmark Optimization & Readiness

## Objectives
1) **Academic Benchmarks (must hit before any open-source packaging)**
   - SciERC **F1_micro ≥ 0.50** (PURE / PL-Marker)
   - BioRED **entity ≥ 0.90**, **relation ≥ 0.65**
2) **Dataset-Aware Loaders**
   - BioRED: preserve relations; dedup with stable IDs (PMID + section/paragraph offsets)
   - SciERC: robust split handling; unify dev/test receipts
3) **CI Gates & Scoreboards**
   - Enforce governance **and** benchmark thresholds in CI
   - Publish receipts-driven leaderboards in `docs/scoreboards/phase8/`

## Deliverables
- Receipts for PURE and PL-Marker runs on SciERC (dev/test) & BioRED (full).
- Updated `docs/scoreboards/phase8/` with metrics & provenance.
- Loader fixes merged (no over-collapse; no relation loss).
- Architect summary with competitor framing (ChatGPT/Claude): governance **plus** accuracy.

## Non-Goals (Phase 8)
- No open-source packaging or `main` merge until targets are met and receipts are published.

