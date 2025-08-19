from __future__ import annotations
import os
from neo4j import GraphDatabase


class Graph:
    def __init__(self):
        self.uri = os.getenv("NEO4J_URL", "bolt://localhost:7687")
        self.user = os.getenv("NEO4J_USER", "neo4j")
        self.pw = os.getenv("NEO4J_PASSWORD", "neo4jpass123")
        self.driver = GraphDatabase.driver(self.uri, auth=(self.user, self.pw))

    def close(self):
        if self.driver:
            self.driver.close()

    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc, tb):
        self.close()

    def mirror_draft(
        self,
        *,
        draft: dict,
        manifest: dict,
        mirror_spans: bool = True,
        max_spans: int | None = None,
    ):
        user_id = draft["user_id"]
        doc_digest = draft["doc_digest"]
        manifest_digest = draft["manifest"]["digest"]
        spans = manifest.get("spans", [])
        if max_spans is not None:
            spans = spans[:max_spans]

        with self.driver.session() as s:
            if mirror_spans and spans:
                s.run(
                    """
                    MERGE (u:User {uid:$user_id})
                    MERGE (d:Document {digest:$doc_digest})
                    MERGE (m:Manifest {digest:$manifest_digest})
                    MERGE (u)-[:OWNS]->(d)
                    MERGE (d)-[:HAS_MANIFEST]->(m)
                    WITH m, $spans AS spans
                    UNWIND spans AS sp
                      MERGE (s:Span {sid: sp.id})
                      ON CREATE SET s.start = sp.start, s.end = sp.end
                      MERGE (m)-[:HAS_SPAN]->(s)
                    RETURN 1
                """,
                    user_id=user_id,
                    doc_digest=doc_digest,
                    manifest_digest=manifest_digest,
                    spans=[
                        {"id": s["id"], "start": s["start"], "end": s["end"]}
                        for s in spans
                    ],
                ).consume()
            else:
                s.run(
                    """
                    MERGE (u:User {uid:$user_id})
                    MERGE (d:Document {digest:$doc_digest})
                    MERGE (m:Manifest {digest:$manifest_digest})
                    MERGE (u)-[:OWNS]->(d)
                    MERGE (d)-[:HAS_MANIFEST]->(m)
                    RETURN 1
                """,
                    user_id=user_id,
                    doc_digest=doc_digest,
                    manifest_digest=manifest_digest,
                ).consume()
