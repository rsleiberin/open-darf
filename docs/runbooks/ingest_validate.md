# DARF Runbook: Ingest → Show → Validate (Gate 1.3)

Prerequisites:
- Services running: MinIO (CAS), Qdrant, Neo4j.
- Python venv with: boto3, neo4j==5.22.0.
- .env.local configured:
  - MINIO_ENDPOINT, MINIO_ACCESS_KEY, MINIO_SECRET_KEY, MINIO_BUCKET
  - QDRANT_URL, QDRANT_COLLECTION
  - NEO4J_URL, NEO4J_USER, NEO4J_PASSWORD

One-time (Neo4j schema):
    python apps/validator/init_schema.py
    # prints: schema: ok

Ingest (builds manifest + stores CAS pointer-only draft):
    python apps/transform/ingest.py --file /path/to/file.txt --user u123 --auth-class owner
    # prints JSON containing draft.draft_path under var/drafts/*.json

Show (preview spans):
    python apps/transform/show.py --draft var/drafts/XXXX.json

Validate (strict perf targets; uses L1 CAS cache in var/cas):
    # strict without spans (first run may include S3 read)
    python apps/validator/validator.py --draft var/drafts/XXXX.json --strict --no-spans

    # strict with capped spans (should be <170 ms on warm/hot path)
    python apps/validator/validator.py --draft var/drafts/XXXX.json --strict --max-spans 10

Notes:
- L1 CAS cache lives in var/cas/; after the first S3 read, subsequent validations use local cache.
- Perf gates (strict):
  - Cold: target ≤170 ms (may be close if first S3 read occurs).
  - Warm/Hot (L1): typically 10–150 ms depending on span count and CPU.
- Latest validation audit is written as var/audit/*-validation.json.
