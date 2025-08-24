# Provenance Startup Wiring (Neo4j)

- apps/provenance/driver.py#get_driver() reads NEO4J_URI, NEO4J_USER, NEO4J_PASSWORD and lazy-imports the neo4j package.
- apply_startup_schema(driver) calls apps/provenance/schema.py::apply_constraints(driver); it is idempotent.
- Tests mock the "neo4j" package and never open a network connection.

## Env (example)

    export NEO4J_URI=bolt://localhost:7687
    export NEO4J_USER=neo4j
    export NEO4J_PASSWORD=please_set_me
