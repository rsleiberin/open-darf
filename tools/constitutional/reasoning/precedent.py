from __future__ import annotations
import json, os
from typing import Dict, Iterable, List, Optional, Tuple

def _jaccard(a: Iterable[str], b: Iterable[str]) -> float:
    sa, sb = set(a), set(b)
    if not sa and not sb: return 1.0
    if not sa or not sb: return 0.0
    inter = len(sa & sb); union = len(sa | sb)
    return (inter / union) if union else 0.0

class PrecedentStore:
    def upsert(self, precedent_id: str, principles: List[str], rationale: str, decision: str | None = None) -> None: ...
    def find_similar(self, principles: List[str], topk: int = 3) -> List[str]: ...
    def get(self, precedent_id: str) -> Optional[Dict]: ...

class LocalPrecedentStore(PrecedentStore):
    def __init__(self, path: str = "var/state/precedents.jsonl") -> None:
        self.path = path
        os.makedirs(os.path.dirname(self.path), exist_ok=True)
        if not os.path.exists(self.path):
            with open(self.path, "w", encoding="utf-8") as f: pass

    def _load(self) -> List[Dict]:
        items: List[Dict] = []
        with open(self.path, "r", encoding="utf-8") as f:
            for line in f:
                line = line.strip()
                if not line: continue
                try:
                    items.append(json.loads(line))
                except json.JSONDecodeError:
                    continue
        return items

    def _write_all(self, items: List[Dict]) -> None:
        tmp = self.path + ".tmp"
        with open(tmp, "w", encoding="utf-8") as f:
            for it in items:
                f.write(json.dumps(it, ensure_ascii=False) + "\n")
        os.replace(tmp, self.path)

    def upsert(self, precedent_id: str, principles: List[str], rationale: str, decision: str | None = None) -> None:
        items = self._load()
        for it in items:
            if it.get("id") == precedent_id:
                it["principles"] = principles
                it["rationale"] = rationale
                it["decision"] = decision
                self._write_all(items)
                return
        items.append({"id": precedent_id, "principles": principles, "rationale": rationale, "decision": decision})
        self._write_all(items)

    def find_similar(self, principles: List[str], topk: int = 3) -> List[str]:
        items = self._load()
        scored: List[Tuple[float, str]] = []
        for it in items:
            score = _jaccard(principles, it.get("principles", []))
            scored.append((score, it.get("id")))
        scored.sort(key=lambda x: (-x[0], x[1] or ""))
        return [pid for _, pid in scored[:topk] if pid]

    def get(self, precedent_id: str) -> Optional[Dict]:
        for it in self._load():
            if it.get("id") == precedent_id:
                return it
        return None

class Neo4jPrecedentStore(PrecedentStore):
    """
    Lazily initialized Neo4j-backed store. Requires env:
      NEO4J_URI, NEO4J_USER, NEO4J_PASSWORD
    Falls back to LocalPrecedentStore if driver/env unavailable.
    """
    def __init__(self) -> None:
        self._driver = None
        self._fallback = LocalPrecedentStore()
        uri = os.getenv("NEO4J_URI"); user = os.getenv("NEO4J_USER"); pwd = os.getenv("NEO4J_PASSWORD")
        if uri and user and pwd:
            try:
                from neo4j import GraphDatabase  # type: ignore
                self._driver = GraphDatabase.driver(uri, auth=(user, pwd))
            except Exception:
                self._driver = None

    def upsert(self, precedent_id: str, principles: List[str], rationale: str, decision: str | None = None) -> None:
        if not self._driver:
            return self._fallback.upsert(precedent_id, principles, rationale)
        q = "MERGE (p:Precedent {id:$id}) SET p.principles=$principles, p.rationale=$rationale"
        with self._driver.session() as s:
            s.run(q, id=precedent_id, principles=principles, rationale=rationale, decision=decision)

    def find_similar(self, principles: List[str], topk: int = 3) -> List[str]:
        if not self._driver:
            return self._fallback.find_similar(principles, topk)
        q = "MATCH (p:Precedent) RETURN p.id AS id, p.principles AS principles"
        rows: List[Tuple[float, str]] = []
        with self._driver.session() as s:
            for rec in s.run(q):
                rows.append((_jaccard(principles, rec["principles"] or []), rec["id"]))
        rows.sort(key=lambda x: (-x[0], x[1] or ""))
        return [pid for _, pid in rows[:topk] if pid]

    def get(self, precedent_id: str) -> Optional[Dict]:
        if not self._driver:
            return self._fallback.get(precedent_id)
        q = "MATCH (p:Precedent {id:$id}) RETURN p.id AS id, p.principles AS principles, p.rationale AS rationale"
        with self._driver.session() as s:
            rec = s.run(q, id=precedent_id).single()
            return dict(rec) if rec else None
