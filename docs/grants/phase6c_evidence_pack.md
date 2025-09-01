# Phase-6C Evidence Pack (Grants/Reviewers)

- Commit: `a821dfa`
- Session receipt: `var/receipts/phase6c/sessions/20250901-232629/receipt.json`
- CI snapshot: `var/reports/phase6c/ci_runs/20250901-232607`
- Gates: `var/reports/phase6c/gates.json`
- Metrics: `var/receipts/phase6c/validation/metrics.json`

## Headline Metrics (receipt-driven)
| Dataset | Entity F1 | Precision | Recall | Relation F1 |
|---|---:|---:|---:|---:|
| SciERC | 0.30703012912482064 | 0.35785953177257523 | 0.26884422110552764 | – |
| BioRED | 0.6310494357786541 | – | – | 0 |

> Relation F1 for BioRED is recorded for visibility and not a failing gate in Phase-6C.

## Provenance & Audit
- Audit index: `docs/audit/phase6c/`
- Latest CI artifacts (gates + validation inputs): `var/reports/phase6c/ci_runs/20250901-232607`

## Read-me for Reviewers
- CI is hermetic: metrics are rebuilt from committed receipts; no network dependency.
- Gates enforce presence + non-regression of the headline metrics.
- Relation work is being integrated under receipts first; gating may be proposed in a later phase.
