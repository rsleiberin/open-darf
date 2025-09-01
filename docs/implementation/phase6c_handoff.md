# Phase 6C — Technical Recovery Handoff

Status: execution complete; results branch pushed.
Branch: (filled by CI/reviewer)
Date (UTC): (filled by reviewer)

## Artifacts
- Results README: docs/implementation/phase6c_results.md
- Provenance: var/reports/phase6c/prov_export.json
- Validator/gates: var/reports/phase6c/{validation_*.log,gates.json}
- Baseline comparisons: var/reports/phase6c/{scierc_compare.json,biored_compare.json,regressions.json}
- Accuracy digest: var/reports/phase6c/accuracy_digest.json
- Archive: var/reports/phase6c/artifacts_*.tar.gz

## Receipts (latest)
- SciERC: var/receipts/phase6c/validation/scierc/…/
- BioRED: var/receipts/phase6c/validation/biored/…/

## Known deviations
- SciERC and BioRED runs used baseline harnesses; metrics read as zeros by design.
- BioRED dataset is a placeholder split; mirrors failed during session. Do not use for publication.

## Next-session TODO (blocking for publication)
1. Pin official SciERC and BioRED sources with checksums and license notes.
2. Swap baselines for real model inference; re-run with cached GPU stack.
3. Rebuild summaries and validator scores; re-run gates and comparisons.
4. Update docs/implementation/phase6c_results.md with real numbers.

## Re-run mini playbook
- Prepare datasets: scripts/prepare_benchmark.py scierc|biored --out data/<task>
- Run tasks: scripts/run_scierc.py …; scripts/run_biored.py …
- Summarize: scripts/summarize_eval*.py …
- Validate & gates: scripts/validate_accuracy_receipts.sh var/receipts/phase6c/validation; scripts/local_ml_gates.sh …
- Compare & docs: scripts/compare_to_baselines.py …; scripts/generate_results_readme.py …
