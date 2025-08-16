from __future__ import annotations
import os
from neo4j import GraphDatabase

uri = os.getenv("NEO4J_URL", "bolt://localhost:7687")
user = os.getenv("NEO4J_USER", "neo4j")
pw   = os.getenv("NEO4J_PASSWORD", "neo4jpass123")

drv = GraphDatabase.driver(uri, auth=(user, pw))
with drv.session() as s:
    s.run("CREATE CONSTRAINT doc_digest IF NOT EXISTS FOR (d:Document) REQUIRE d.digest IS UNIQUE;")
    s.run("CREATE CONSTRAINT man_digest IF NOT EXISTS FOR (m:Manifest) REQUIRE m.digest IS UNIQUE;")
    s.run("CREATE CONSTRAINT span_id    IF NOT EXISTS FOR (s:Span)     REQUIRE s.sid   IS UNIQUE;")
    s.run("CREATE CONSTRAINT user_id    IF NOT EXISTS FOR (u:User)     REQUIRE u.uid   IS UNIQUE;")
print("schema: ok")
