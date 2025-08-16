from __future__ import annotations
import os, time
from typing import Any, Dict, List
from neo4j import GraphDatabase

class ValidatorClient:
    def __init__(self, uri: str|None=None, user: str|None=None, password: str|None=None) -> None:
        self.uri = uri or os.getenv("NEO4J_URL","bolt://localhost:7687")
        self.user = user or os.getenv("NEO4J_USER","neo4j")
        self.password = password or os.getenv("NEO4J_PASSWORD","neo4jpass123")
        self._driver = GraphDatabase.driver(self.uri, auth=(self.user, self.password))

    def close(self)->None:
        try: self._driver.close()
        except Exception: pass

    def ping(self)->bool:
        with self._driver.session() as s:
            r = s.run("RETURN 1 AS ok").single()
            return bool(r and r["ok"]==1)

    def validate_draft(self, draft: Dict[str, Any]) -> Dict[str, Any]:
        t0 = time.perf_counter()
        msgs: List[str] = []
        ok = True

        # Invariants (updated for span-manifest + per-span Qdrant)
        if not draft.get("user_id"):
            msgs.append("sovereignty:missing-user_id"); ok=False
        if draft.get("status") != "ready_for_review":
            msgs.append("sovereignty:status-must-be-ready_for_review"); ok=False

        cas = (draft.get("cas") or {})
        if not cas.get("digest"):
            msgs.append("transparency:missing-cas-digest"); ok=False

        mn = (draft.get("manifest") or {})
        if not mn.get("digest"):
            msgs.append("transparency:missing-manifest-digest"); ok=False

        qd = (draft.get("qdrant") or {})
        if not qd.get("collection"):
            msgs.append("transparency:missing-qdrant-collection"); ok=False

        if not draft.get("explain"):
            msgs.append("capability:missing-explain"); ok=False
        if not draft.get("draft_id"):
            msgs.append("revocation:missing-draft_id"); ok=False

        with self._driver.session() as s:
            s.execute_write(self._write_audit, draft, ok, msgs)

        latency_ms = (time.perf_counter()-t0)*1000.0
        return {"status": "pass" if ok else "fail", "messages": msgs, "latency_ms": round(latency_ms,2), "engine": "neo4j-lite-audit"}

    @staticmethod
    def _write_audit(tx, draft: Dict[str, Any], ok: bool, msgs: List[str]):
        tx.run("""
        MERGE (u:User {id:$user_id})
        MERGE (d:Draft {id:$draft_id})
          ON CREATE SET d.created_at_ms = $created_at_ms
        MERGE (o:Operation {id:$op_id})
          SET o.type='validate', o.ts_ms=$ts_ms, o.status=$status, o.messages=$messages
        MERGE (u)-[:REQUESTED]->(o)
        MERGE (o)-[:VALIDATES]->(d)
        SET d.status=$draft_status
        """,
        user_id=draft.get("user_id"),
        draft_id=draft.get("draft_id"),
        draft_status=draft.get("status"),
        created_at_ms=draft.get("created_at_ms"),
        op_id=f"validate:{draft.get('draft_id')}:{int(time.time()*1000)}",
        ts_ms=int(time.time()*1000),
        status="pass" if ok else "fail",
        messages=msgs)
