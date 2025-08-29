from __future__ import annotations
import os
import re
from typing import Any, Dict, List


def _allow_load() -> bool:
    return os.getenv("EXTRACTOR_TEXT2NKG", "0") == "1"


def _neutral(reason: str, decision: str = "INDETERMINATE") -> Dict[str, Any]:
    return {
        "summary": "",
        "entities": [],
        "relations": [],
        "temporals": [],
        "guard_trace": [
            {"component": "text2nkg", "status": "skipped", "reason": reason}
        ],
        "reason_code": reason,
        "decision": decision,
    }


def _extract_relations(text: str) -> List[Dict[str, Any]]:
    rels: List[Dict[str, Any]] = []
    t = text
    # Pattern 0: "<A> prevents <B>"
    m0 = re.search(r"\b([A-Za-z0-9_]+)\s+(prevents)\s+([A-Za-z0-9_]+)\b", t, re.I)
    if m0:
        rels.append(
            {
                "subject": m0.group(1),
                "relation": m0.group(2).lower(),
                "object": m0.group(3),
                "confidence": 1.0,
                "source": "text2nkg",
            }
        )
    # Pattern 1: "<X> uses <Y>"
    m = re.search(r"\b([A-Za-z0-9_]+)\s+(uses)\s+([A-Za-z0-9_]+)\b", t, re.I)
    if m:
        rels.append(
            {
                "subject": m.group(1),
                "relation": m.group(2).lower(),
                "object": m.group(3),
                "confidence": 1.0,
                "source": "text2nkg",
            }
        )
    # Pattern 2: arrow "A->B" or "A => B"
    m2 = re.search(r"\b([A-Za-z0-9_]+)\s*(?:-?>|=>)\s*([A-Za-z0-9_]+)\b", t)
    if m2:
        rels.append(
            {
                "subject": m2.group(1),
                "relation": "links_to",
                "object": m2.group(2),
                "confidence": 0.9,
                "source": "text2nkg",
            }
        )
    # Fallback
    if not rels and t.strip():
        toks = re.findall(r"[A-Za-z0-9_]+", t)
        if len(toks) >= 2:
            rels.append(
                {
                    "subject": toks[0],
                    "relation": "related_to",
                    "object": toks[1],
                    "confidence": 0.5,
                    "source": "text2nkg",
                }
            )
    # Ensure 'roles' present for downstream tests
    for _r in rels:
        if "roles" not in _r and "subject" in _r and "object" in _r:
            _r["roles"] = [
                {"name": "subject", "value": str(_r.get("subject", ""))},
                {"name": "object", "value": str(_r.get("object", ""))},
            ]
    # Text2NKG roles normalization
    for _r in rels:
        roles = _r.get("roles") or []
        names = {(x.get("name") or "").lower() for x in roles if isinstance(x, dict)}
        # subject
        if "subject" not in names and "subject" in _r:
            roles.append({"name": "subject", "value": str(_r.get("subject", ""))})
            names.add("subject")
        # predicate (from relation/predicate field)
        pred = _r.get("relation") or _r.get("predicate") or ""
        if "predicate" not in names and pred != "":
            roles.append({"name": "predicate", "value": str(pred)})
            names.add("predicate")
        # object
        if "object" not in names and "object" in _r:
            roles.append({"name": "object", "value": str(_r.get("object", ""))})
            names.add("object")
        _r["roles"] = roles

    return rels


def extract(text: str) -> Dict[str, Any]:
    # 1) Short-circuit on empty text (guard requirement)
    if not (text or "").strip():
        return _neutral("empty_text", decision="DENY")
    # 2) Flag OFF -> neutral skip
    if not _allow_load():
        return _neutral("disabled")
    # 3) Simple heuristic relations (service-free)
    rels = _extract_relations(text)
    return {
        "summary": f"{len(rels)} relation(s)" if rels else "",
        "entities": [],
        "relations": rels,
        "temporals": [],
        "guard_trace": [{"component": "text2nkg", "status": "ran", "reason": "ok"}],
        "reason_code": "ok" if rels else "no_relations",
        "decision": "INDETERMINATE",
    }


class Text2NKGExtractor:
    def __call__(self, text: str) -> Dict[str, Any]:
        return extract(text)

    def extract(self, text: str) -> Dict[str, Any]:
        return extract(text)

    @staticmethod
    def extract_static(text: str) -> Dict[str, Any]:
        return extract(text)


__all__ = ["Text2NKGExtractor", "extract"]

# Appended by Phase6B at 20250828-062956


# === Phase6B extension: simple relation extractor (appended) ===
def extract_relations_simple(text: str):
    """
    Patterns supported:
      - "<subj> causes <obj>"
      - "<obj> is caused by <subj>"  -> normalized to causes
      - "<subj> treats <obj>"
      - "<obj> is treated by <subj>" -> normalized to treats
      - "<A> associated with <B>"     -> bidirectional A<->B
    Returns list of relation dicts per contract.
    """
    import re

    def _mk_rel(s, p, o):
        s, o = s.strip(), o.strip()
        return {
            "subject": s,
            "relation": p,
            "object": o,
            "confidence": 1.0,
            "source": "text2nkg",
            "roles": [
                {"name": "subject", "value": s},
                {"name": "predicate", "value": p},
                {"name": "object", "value": o},
            ],
        }

    if not text or not isinstance(text, str):
        return []
    t = text.strip()
    active = [
        (re.compile(r"^\s*(?P<subj>.+?)\s+causes\s+(?P<obj>.+?)\s*$", re.I), "causes"),
        (re.compile(r"^\s*(?P<subj>.+?)\s+treats\s+(?P<obj>.+?)\s*$", re.I), "treats"),
        (
            re.compile(r"^\s*(?P<subj>.+?)\s+associated with\s+(?P<obj>.+?)\s*$", re.I),
            "associated with",
        ),
    ]
    passive = [
        (
            re.compile(
                r"^\s*(?P<obj>.+?)\s+is\s+caused\s+by\s+(?P<subj>.+?)\s*$", re.I
            ),
            "causes",
        ),
        (
            re.compile(
                r"^\s*(?P<obj>.+?)\s+is\s+treated\s+by\s+(?P<subj>.+?)\s*$", re.I
            ),
            "treats",
        ),
    ]
    for pat, pred in active:
        m = pat.match(t)
        if m:
            subj, obj = m.group("subj"), m.group("obj")
            rels = [_mk_rel(subj, pred, obj)]
            if pred == "associated with":
                rels.append(_mk_rel(obj, "associated with", subj))
            return rels
    for pat, pred in passive:
        m = pat.match(t)
        if m:
            subj, obj = m.group("subj"), m.group("obj")
            return [_mk_rel(subj, pred, obj)]
    return []


# === Phase6B observability: text2nkg ===
try:
    from apps.observability.metrics import start_timer, stop_timer, inc, _OBS_ON
except Exception:
    start_timer = stop_timer = lambda *a, **k: None  # type: ignore
    _OBS_ON = False


def _obs_wrap_text2nkg(fn):
    def _inner(*args, **kwargs):
        t = start_timer("text2nkg")
        try:
            out = fn(*args, **kwargs)
            if _OBS_ON and isinstance(out, list):
                inc("text2nkg", "calls")
                # record number of relations produced
                inc("text2nkg", f"relations_{len(out)}")
            return out
        finally:
            stop_timer(t)

    return _inner


if "extract_relations_simple" in globals():
    extract_relations_simple = _obs_wrap_text2nkg(extract_relations_simple)  # type: ignore

# --- Phase6B timing wrapper: text2nkg ---
try:
    import os
    import time
    from apps.observability import metrics as _obs_m

    _PERF_ON_TX = os.getenv("RUN_PERF", "0") == "1"
    _orig_extract_relations_simple = extract_relations_simple  # type: ignore[name-defined]

    def extract_relations_simple(*a, **kw):  # noqa: F811
        if not _PERF_ON_TX or not hasattr(_obs_m, "record_time"):
            return _orig_extract_relations_simple(*a, **kw)
        t0 = time.perf_counter()
        try:
            return _orig_extract_relations_simple(*a, **kw)
        finally:
            _obs_m.record_time("text2nkg", time.perf_counter() - t0)

except Exception:
    pass
# --- End timing wrapper ---


# --- Phase6B: timer wrapper (idempotent, no extra imports) ---
try:
    from apps.observability import metrics as _obs_metrics
except Exception:  # fallback noop

    class _Noop:
        def __call__(self, *_a, **_k):
            return self

        def __enter__(self):
            return None

        def __exit__(self, exc_type, exc, tb):
            return False

    _obs_metrics = type("M", (), {"timer": lambda *_a, **_k: _Noop()})()

try:
    _extract_relations_simple_real = extract_relations_simple

    def extract_relations_simple_timer_wrapped(text: str):
        with _obs_metrics.timer("text2nkg"):
            return _extract_relations_simple_real(text)

    extract_relations_simple = extract_relations_simple_timer_wrapped  # override
except Exception:
    pass
