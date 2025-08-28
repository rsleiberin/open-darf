# Phase 6 — SciBERT Extractor Integration

**Status:** Bootstrap complete. Default OFF via `EXTRACTOR_SCI=0`.
**Local enable (after installing ML deps):**
- `bash tools/ml/install_scibert.sh`
- `export EXTRACTOR_SCI=1`
- Optional: `export RUN_SCI_SMOKE=1` to run smoke test.

**Model IDs:**
- NER default: `dslim/bert-base-NER` (override with `SCIBERT_NER_MODEL_ID`).
- Target fine-tune: SciBERT-based NER for scientific/policy corpora.

**Guarding:** Extractor returns `decision=INDETERMINATE`. Constitutional guard composes final tri-state.

**Perf notes:** Keep simple-query target <50ms when cached; initial load is amortized and excluded from CI.
