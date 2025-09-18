# Lesson 2 — Your Local Stack

We run four services:

- **MinIO** (object storage) — health at /minio/health/live  
- **Qdrant** (vector DB) — health at /healthz  
- **Postgres** (SQL DB) — `pg_isready`  
- **Neo4j** (graph DB) — `cypher-shell "RETURN 1;"`

Why Neo4j *bare-run*? It avoids Compose env pitfalls. Compose still runs the other DBs.

**Check yourself**
~~~bash
bash ./scripts/validator_acceptance.sh
~~~
