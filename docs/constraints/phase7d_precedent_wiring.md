# Phase 7D — Precedent Wiring

- Env flags:
  - `REASONING_ENABLE=1` turns on audit enrichment with explanations.
  - `REASONING_PRECEDENT_WRITE=1` enables writebacks to the precedent store.
  - `REASONING_PRECEDENT_PATH` sets local JSONL path (default `var/state/precedents.jsonl`).
  - `NEO4J_URI/NEO4J_USER/NEO4J_PASSWORD` switch to Neo4j-backed store automatically.
- Enrichment cites up to 3 similar precedents by Jaccard over principle sets.
- Writebacks are idempotent upserts keyed by `precedent_id`.
