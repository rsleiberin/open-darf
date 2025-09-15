# Phase 7T Provenance: Quick Guide

Goal: strengthen evidence integrity with cryptographic anchors and receipts while keeping Phase 7S flows unchanged. This layer is additive.

Canonicalization rules for text before hashing:
- Encode UTF-8
- Convert line endings to LF
- Trim trailing spaces and tabs

Binary files are hashed as-is.

Quick verify on any Ubuntu with Python 3:
$ make verify-provenance
This will:
1) Hash target paths (default: docs/phase7s)
2) Validate the manifest schema
3) Store objects in local CAS at .cas/sha256
4) Emit audited receipts under docs/audit/phase7t

Choose custom targets:
$ make verify-provenance paths="docs/phase7s scripts"

Local CAS facts:
- Object name is the SHA-256 digest
- Identical content deduplicates automatically
- Receipts include stored_new and dedup_hits

Optional MinIO integration (if configured in env and mc is installed):
- MINIO_URL, MINIO_ACCESS_KEY, MINIO_SECRET_KEY, MINIO_BUCKET
- Objects stored at sha256/<digest>

Backwards compatibility:
- No changes to Phase 7S command surfaces
- Legacy bundles remain valid
- New files live under docs/phase7t/ and docs/audit/phase7t/

Receipts:
- JSON with schema_version = 1
- provenance.algorithm = sha256
- provenance.canonicalization = utf8+lf+trim-trailing
- links include manifest path and suggested verify commands
