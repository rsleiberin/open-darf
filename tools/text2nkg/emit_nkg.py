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

# === DARF Phase7b: span validator (idempotent append) ===
from typing import Iterable, Mapping, List, Tuple, Optional

def _get_first(d: Mapping, *keys):
  for k in keys:
    if k in d:
      return d[k]
  return None

def assert_valid_spans(spans: Optional[Iterable[Mapping]]) -> Tuple[List[dict], int]:
  """
  Normalize and validate span shapes for exporter.

  Input:
    spans: iterable of mappings with at least start/end (or known aliases) and optional label.

  Behavior:
    - Accepts aliases for bounds: ('start','begin','offset_start','char_start'), ('end','stop','offset_end','char_end')
    - Accepts label aliases: ('label','type','tag','category')
    - Produces list[dict] with keys: start(int), end(int), label(str|None)
    - Keeps order; skips invalid items; returns (ok_spans, skipped_count)
    - Valid iff: start and end are integers, start >= 0, end > start
  """
  ok: List[dict] = []
  bad = 0
  if spans is None:
    return ok, bad

  for s in spans:
    if not isinstance(s, Mapping):
      bad += 1
      continue

    start = _get_first(s, "start", "begin", "offset_start", "char_start")
    end   = _get_first(s, "end", "stop", "offset_end", "char_end")
    label = _get_first(s, "label", "type", "tag", "category")

    # Coerce numeric strings to int where safe
    try:
      if isinstance(start, str) and start.isdigit():
        start = int(start)
      if isinstance(end, str) and end.isdigit():
        end = int(end)
    except Exception:
      pass

    if isinstance(start, int) and isinstance(end, int) and start >= 0 and end > start:
      ok.append({"start": start, "end": end, "label": label if (label is None or isinstance(label, str)) else str(label)})
    else:
      bad += 1

  return ok, bad
