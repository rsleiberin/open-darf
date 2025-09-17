# SciERC Dataset Stub (A3)
This is a scaffold for real SciERC processing. No mock validation is performed.
- Evidence, timings, and receipts are recorded via Postgres.
- Vector ops go to Qdrant; graph ops to Neo4j; artifacts to MinIO when available.
