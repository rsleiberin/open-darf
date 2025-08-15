# Constitutional Validator — Neo4j Schema (Issue #201)

Nodes: `User(id)`, `SMG(id)`, `Constraint(key,type)`, `Operation(id,kind)`, `Decision(id)`
Rels: `OWNS`, `GOVERNS`, `APPLIES_TO`, `PRODUCES`, `AUDITS`

Load constraints & indexes:

    NEO4J_URI=bolt://localhost:7687 NEO4J_USER=neo4j NEO4J_PASSWORD=pass \
      python apps/validator/neo4j/load_schema.py

Install deps:

    python -m venv .venv && source .venv/bin/activate && pip install -r apps/validator/neo4j/requirements.txt
