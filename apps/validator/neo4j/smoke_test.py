import os
from neo4j import GraphDatabase

uri = os.getenv("NEO4J_URI", "bolt://localhost:7687")
user = os.getenv("NEO4J_USER", "neo4j")
pwd = os.getenv("NEO4J_PASSWORD", "neo4jpass123")
db = os.getenv("NEO4J_DB", "neo4j")

drv = GraphDatabase.driver(uri, auth=(user, pwd))
with drv.session(database=db) as s:
    cons = s.run("SHOW CONSTRAINTS").data()
    idxs = s.run("SHOW INDEXES").data()
    print(f"constraints={len(cons)} indexes={len(idxs)}")
drv.close()
