# Graph Storage Architecture (Phase-4)

## Modeling choice
We adopt a **hyperedge node** for n-ary relations:

- `(e:Entity {uid, etype, name, props})`
- `(h:HyperEdge {uid, relation, props})`
- `(h)-[:PARTICIPATES {role}]->(e)`

This avoids multi-rel reification bloat and keeps roles explicit.

## Neo4j constraints & indexes (Neo4j 5)
- `Entity.uid` UNIQUE
- `HyperEdge.uid` UNIQUE
- BTREE indexes:
  - `Entity(etype)`
  - `Entity(name)` (string)
  - `HyperEdge(relation)`

## Qdrant collection (vector search)
- Collection: `facts`
- Vector size: **parametric** (env: `QDRANT_D`, default 384)
- Distance: `Cosine`
- HNSW: `M=16`, `ef_construct=128`
- Payload keys (examples): `doc_id`, `chunk_id`, `relation`, `participants` (list of entity uids)

## Perf budget
- Query p95: **< 50 ms** end-to-end (vector search + graph fanout for roles).
- Baselines captured via receipts under `docs/audit/*`.

## Compliance hooks
All graph writes must consult `evaluate_action(...)` (fail-closed). The `GuardedGraphStore` enforces this around:
- `upsert_entity`, `upsert_hyperedge`, `relate`.
