
## Demo procedure (local)

1. Run unit tests for Phase 7C:
   - pytest -q tests/phase7c

2. Create a demo set and tag it:
   - python -m tools.constitutional.document_tagger --in var/receipts/phase7c/demo_*/docs.jsonl --out-tags var/receipts/phase7c/demo_*/tags.jsonl --blocklist blocked --audit-stdout > var/receipts/phase7c/demo_*/audit_tagger.jsonl

3. Enforce fail-closed filtering:
   - python -m tools.constitutional.constitutional_filter --in var/receipts/phase7c/demo_*/docs.jsonl --tags var/receipts/phase7c/demo_*/tags.jsonl --out-accepted var/receipts/phase7c/demo_*/accepted.jsonl --audit-stdout > var/receipts/phase7c/demo_*/audit_filter.jsonl

4. Generate a blocking effectiveness report:
   - python -m tools.constitutional.report_blocking --audits var/receipts/phase7c/demo_*/audit_tagger.jsonl var/receipts/phase7c/demo_*/audit_filter.jsonl --out var/receipts/phase7c/demo_*/report_blocking.json

Artifacts appear under `var/receipts/phase7c/demo_*`.
