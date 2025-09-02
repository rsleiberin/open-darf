import json, time, hashlib
from typing import Dict, Any, Iterable

def sha256_bytes(b: bytes) -> str:
    h=hashlib.sha256(); h.update(b); return h.hexdigest()

def emit_nkg(sentences: Iterable[Dict[str,Any]], preds: Iterable, run_meta: Dict[str,Any]) -> Dict[str,Any]:
    nodes, edges = [], []
    node_id = 0
    for s, p in zip(sentences, preds):
        sid = s.get("sid")
        for sp in getattr(p, "spans", []):
            nid = node_id; node_id += 1
            nodes.append({"id": nid, "sid": sid, "start": sp.get("start"), "end": sp.get("end"), "label": sp.get("label")})
        base = node_id - len(getattr(p, "spans", []))
        for r in getattr(p, "relations", []):
            edges.append({"h": base + r.get("h"), "t": base + r.get("t"), "type": r.get("type","UNK"), "sid": sid})
    payload = {"run": run_meta, "nodes": nodes, "edges": edges, "timestamp": time.time()}
    payload["sha256"] = sha256_bytes(json.dumps(payload, sort_keys=True).encode("utf-8"))
    return payload
