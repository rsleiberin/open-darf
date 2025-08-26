# N-ary Relationship Modeling (Hyperedge pattern)

## Why hyperedges
- Avoids proliferation of intermediate nodes per binary relation.
- Preserves role semantics explicitly on edges from HyperEdge → Entity.

## Pattern
    (h:HyperEdge {uid, relation, props})
    (e:Entity {uid, etype, name})
    (h)-[:PARTICIPATES {role:"subject"}]->(e)
    (h)-[:PARTICIPATES {role:"object"}]->(e)

## Examples
- works_at(subject=Person, object=Org, when=2022-present)
- acquired(acquirer=Org, acquiree=Org, date=2024-07-01, price=1.2e9)

## Trade-offs
- Pros: role clarity; single place for n-ary attributes; simpler fanout.
- Cons: join cost during retrieval; requires role indexes if heavy.

## Index guidance (Neo4j 5)
- CONSTRAINT: Entity.uid UNIQUE; HyperEdge.uid UNIQUE
- INDEX: HyperEdge(relation); Entity(etype), Entity(name)
