# Install: Enhanced Mode (Phase 7T)

This guide adds provenance anchoring alongside your existing Phase 7S setup. It is additive; 7S continues to work unchanged.

Requirements (basic):
- Ubuntu with Python 3
- make
- Optional: jq for JSON checks

Optional (MinIO feature):
- 'mc' CLI installed
- Environment variables: MINIO_URL, MINIO_ACCESS_KEY, MINIO_SECRET_KEY, MINIO_BUCKET

Quick Start (enhanced verify):
$ make verify-provenance
Result: hashes your targets (default: docs/phase7s), validates the manifest, stores objects in local CAS (.cas/sha256), and writes audited receipts under docs/audit/phase7t.

Custom paths:
$ make verify-provenance paths="docs/phase7s scripts"

QA/Perf timing:
$ make qa-provenance

Help:
$ make help-provenance

MinIO readiness (optional):
$ scripts/phase7t/minio_check.sh
If all checks pass, re-run the MinIO round-trip step.
