# RCA — Benchmark Gold Unavailable for Scoring (Phase-7A)

**Symptom:** Scorer produced `gold_not_found_or_empty` for BioRED/SciERC dev/test.

**Root Cause:** Candidate JSONL files currently present:
- `var/datasets/normalized/biored_concept/{dev,test}.jsonl` — concept-level; no per-sentence mention spans.
- `var/datasets/text/scierc_by_sentence/{dev,test}.jsonl` — sentence texts only; no entities.

**Impact:** Group 1.2 (benchmark reproduction) blocked.

**Interim Unblock:** Use Phase-6C toy BioRED JSONL as temporary gold under `var/datasets/text/biored_by_sentence/{dev,test}.jsonl` to validate the scoring harness end-to-end (receipt-anchored). This is a *sanity* gate, not a benchmark.

**Next Steps (replace toy with true gold):**
1. Locate / provision sentence-level entity gold for BioRED and SciERC (span offsets).
2. Add schema adapters as needed (extend `tools/text2nkg/gold_utils.py`).
3. Lock hashes and produce receipts; re-run scorer to populate real P/R/F1.
