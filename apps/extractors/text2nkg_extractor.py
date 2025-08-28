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
