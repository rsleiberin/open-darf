# Phase 7G — Reviewer Checklist

**Generated:** 2025-09-08T19:38:10Z

## Acceptance Gates (must hold)
- Relation Extraction smoke gate: **F1_micro ≥ 0.20** and **compliance ≥ 0.95**
- Metrics receipts conform to **schemas/metrics_v1.json**

### Source-of-truth Metrics
- Baseline (best): `var/receipts/phase7g/relation_baseline/run/20250907-205327_v6/metrics.json`

### Recent Receipts
- Finalize summary dir: `var/receipts/phase7g/finalize/20250908-192059`
- Latest Packaging/Lifecycle smoke: `var/receipts/phase7g/packaging_smoke/20250908-183142`
- Latest PURE bridge: `var/receipts/phase7g/pure_runs/20250908-052010`
- Latest PL-Marker bridge: `var/receipts/phase7g/plmarker_runs/20250908-051836`

---

## PR #384 — RE Baseline (E1 pass)
- [ ] Confirm baseline metrics file present and matches docs (see above)
- [ ] Verify docs: `docs/phase7g/RE_E1_MILESTONE.md`, `docs/phase7g/STATUS.md`
- [ ] Gate logic present in `scripts/relex_ci_smoke.py` (≥0.20 & ≥0.95)
- Decision: **ALLOW / DENY / INDETERMINATE**

## PR #385 — Config + CI validation
- [ ] CI workflows: config-validate, relex-smoke, packaging-smoke exist and pass
- [ ] Metrics schema & validator present; receipts validate
- [ ] E2E bootstrap smoke passes locally (receipt noted in STATUS)
- Decision: **ALLOW / DENY / INDETERMINATE**

## PR #386 — PURE baseline (draft)
- [ ] PURE/PL-Marker runners + bridge wrappers present
- [ ] Label-gated CI ready; bridges import baseline metrics if deps missing
- [ ] Keep **DRAFT** until real baselines run (optional)
- Decision (draft): **ACK / REQUEST CHANGES**

---

## Notes
- Universal parser normalized spans (end-exclusive); error-analysis notes updated.
- Packaging stub no longer emits schema-breaking metrics; legacy receipts backfilled to schema v1.

