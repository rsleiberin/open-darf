#!/usr/bin/env python3
import json
from typing import Dict, Any, Iterable

def _as_text(x):
    if isinstance(x, dict):
        for k in ("text","name","span"):
            if k in x and x[k]:
                return str(x[k])
        return json.dumps(x, ensure_ascii=False)
    if isinstance(x, (list, tuple)):
        return " ".join(map(str, x))
    return "" if x is None else str(x)

def normalize_item(obj: Dict[str, Any]) -> Dict[str, Any]:
    head = obj.get("head") or obj.get("h") or obj.get("subject") or obj.get("subj")
    tail = obj.get("tail") or obj.get("t") or obj.get("object") or obj.get("obj")
    rel  = obj.get("relation") or obj.get("rel") or obj.get("label") or obj.get("type")

    head = _as_text(head) if not isinstance(head, str) else head
    tail = _as_text(tail) if not isinstance(tail, str) else tail
    rel  = "" if rel is None else (rel if isinstance(rel, str) else _as_text(rel))

    return {"head": head.strip(), "tail": tail.strip(), "relation": rel.strip()}

def load_any(path: str) -> Iterable[Dict[str, Any]]:
    import pathlib
    p = pathlib.Path(path)
    txt = p.read_text(encoding="utf-8").strip()
    if not txt:
        return []
    if txt.startswith("["):
        return [normalize_item(x) for x in json.loads(txt)]
    if txt.startswith("{"):
        return [normalize_item(json.loads(txt))]
    return [normalize_item(json.loads(line)) for line in txt.splitlines() if line.strip()]
