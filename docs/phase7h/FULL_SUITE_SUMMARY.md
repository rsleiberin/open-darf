# Full-Suite E2E Summary — 2025-09-09 03:06:28Z

This report consolidates ingest→dedup→removal→re-eval receipts for **all datasets** discovered under `var/receipts/phase7h/full_suite/*/*`.

## Datasets Overview

| dataset | docs: pre → ingest → dedup → post-removal | rels: ingest → dedup → post-removal | timings (ms): ingest / dedup / resynth | F1 / Compliance | pred_count | flags |
|---|---|---|---|---|---|---|
| biored_norm | 0 → 587 → 1 → 582 | 9300 → 48 → 9168 | 127.856 / 52.177 / 46.092 | 1.0 / 1.0 | 9168 | REMOVAL_INCREASED_DOCS, DEDUP_TOO_AGGRESSIVE |
| biored_official | 0 → 1988 → 203 → 1969 | 16712 → 0 → 16712 | 404.343 / 279.127 / 190.957 | 1.0 / 1.0 | 16712 | REMOVAL_INCREASED_DOCS, DEDUP_ZEROED_RELATIONS |
| scierc | 0 → 1 → 1 → 0 | 0 → 0 → 0 | 104.896 / 21.581 / 20.291 | 1.0 / 1.0 | 0 |  |
| scierc_json | 0 → 500 → 500 → 495 | 4648 → 4648 → 4615 | None / None / None | 1.0 / 1.0 | 4615 |  |
| scierc_norm | 0 → 500 → 500 → 495 | 4648 → 4648 → 4615 | 97.585 / 39.201 / 46.7 | 1.0 / 1.0 | 4615 |  |

## Data Normalization Notes & Recommendations
- **BIORED_OFFICIAL**: `post_dedup` shows `rels=0` despite `post_ingest` having relations. Likely relation annotations live in format-specific fields or separate files. **Action:** add dataset-aware loader to join relations before recount in dedup snapshot.
- **BIORED_NORM**: `post_dedup docs=1` after ingest of 587 docs suggests over-aggressive exact hashing (many identical normalized text blocks). **Action:** include stable identifiers (e.g., PMID + section + paragraph offsets) in the content hash, or hash at paragraph/chunk granularity.
- **SCIERC (norm/json)**: flows look healthy (500 → 500 → ~495) with small, controlled removal; relations/ents decrease proportionally. **No action** beyond swapping in real evaluators (heuristic/PURE/PL-Marker).

## Governance & Performance
- All datasets achieved **compliance = 1.0** under the identity evaluator; timings remain modest (hundreds of ms per phase), suitable for governance workflows.
- Next accuracy step: run **heuristic baseline** or **PURE/PL-Marker** within the same receipts for SciERC/BioRED and update this report.
