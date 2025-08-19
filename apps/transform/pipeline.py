from __future__ import annotations
import json
import os
import time
import uuid
import math
from pathlib import Path
from typing import Dict, Any
from apps.storage.minio_cas import MinioCAS, CasRef
from apps.search.qdrant_client import QdrantSearch


def _embed3(text: str) -> list[float]:
    L = len(text)
    s = text.count(" ")
    a = sum(ch.isalnum() for ch in text)
    v = [float(L), float(s), float(a)]
    n = (L * L + s * s + a * a) ** 0.5 or 1.0
    return [x / n for x in v]


def _provenance_default(file_path: str, collector: str) -> dict:
    from datetime import datetime, timezone

    return {
        "source_kind": "upload",
        "source_locator": file_path,
        "collected_at": datetime.now(timezone.utc).isoformat(),
        "collector": collector,
    }


DRAFT_DIR = Path("var/drafts")
AUDIT_DIR = Path("var/audit")
DRAFT_DIR.mkdir(parents=True, exist_ok=True)
AUDIT_DIR.mkdir(parents=True, exist_ok=True)


def _now_ms():
    return int(time.time() * 1000)


def _embed3(text: str) -> list[float]:
    # simple 3-dim embedding: [len, spaces, alnum] normalized
    L = len(text)
    s = text.count(" ")
    a = sum(ch.isalnum() for ch in text)
    v = [float(L), float(s), float(a)]
    n = math.sqrt(sum(x * x for x in v)) or 1.0
    return [x / n for x in v]


def _audit(event: str, data: Dict[str, Any]) -> None:
    rec = {"ts_ms": _now_ms(), "event": event, **data}
    with open(AUDIT_DIR / f"{_now_ms()}_{event}.jsonl", "a") as f:
        f.write(json.dumps(rec) + "\n")


def ingest(file_path: str, user_id: str, intent_anchor: str | None = None) -> Path:
    p = Path(file_path).expanduser().resolve()
    content = p.read_bytes()
    cas = MinioCAS()
    ref: CasRef = cas.put_bytes(content, content_type="text/plain")
    vec = _embed3(content.decode("utf-8", errors="ignore"))
    q = QdrantSearch()
    q.ensure_collection(dim=3, distance="Cosine")
    point_id = q.upsert(vec, {"anchor_id": ref.digest, "user_id": user_id})
    draft = {
        "draft_id": str(uuid.uuid4()),
        "status": "ready_for_review",  # gating: we do NOT auto-apply
        "user_id": user_id,
        "origin": {
            "file": str(p),
            "bytes": len(content),
            "intent_anchor": intent_anchor,
        },
        "cas": {
            "digest": ref.digest,
            "key": f"sha256/{ref.digest[:2]}/{ref.digest[2:4]}/{ref.digest}",
        },
        "qdrant": {
            "point_id": point_id,
            "collection": os.getenv("QDRANT_COLLECTION", "anchors"),
        },
        "created_at_ms": _now_ms(),
        "explain": {"method": "anchors", "embedding_dim": 3},
    }
    out = DRAFT_DIR / f"{draft['draft_id']}.json"
    out.write_text(json.dumps(draft, indent=2))
    _audit(
        "ingest",
        {
            "draft_id": draft["draft_id"],
            "user_id": user_id,
            "digest": ref.digest,
            "point_id": point_id,
        },
    )
    return out


def validate(draft_path: str) -> Path:
    p = Path(draft_path)
    draft = json.loads(p.read_text())
    # Place-holder: real Neo4j constitutional checks will be wired next
    draft["validated_at_ms"] = _now_ms()
    draft["validation"] = {
        "status": "pass",
        "by": "placeholder",
        "notes": "validator wiring to follow (#204)",
    }
    p.write_text(json.dumps(draft, indent=2))
    _audit("validate", {"draft_id": draft["draft_id"], "status": "pass"})
    return p


def search(text: str, top_k: int, user_id: str | None = None):
    q = QdrantSearch()
    vec = _embed3(text)
    return [
        {"id": r.id, "score": r.score, "payload": r.payload}
        for r in q.query(vec, top_k=top_k, user_id=user_id)
    ]


def validate_neo4j(draft_path: str) -> Path:
    from apps.validator.neo4j_client import ValidatorClient

    p = Path(draft_path)
    draft = json.loads(p.read_text())
    vc = ValidatorClient()
    try:
        result = vc.validate_draft(draft)
    finally:
        vc.close()
    draft["validated_at_ms"] = _now_ms()
    draft["validation"] = result
    p.write_text(json.dumps(draft, indent=2))
    _audit(
        "validate",
        {
            "draft_id": draft["draft_id"],
            "status": result["status"],
            "latency_ms": result["latency_ms"],
        },
    )
    return p
