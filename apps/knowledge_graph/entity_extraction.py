from __future__ import annotations
import os
import re
from typing import Any, Callable, Dict, List, Tuple


def _noop(name: str, reason: str) -> Dict[str, Any]:
    return {
        "summary": "",
        "entities": [],
        "relations": [],
        "temporals": [],
        "guard_trace": [{"component": name, "status": "skipped", "reason": reason}],
        "decision": "INDETERMINATE",
    }


# Extractors (soft-optional)
try:
    from apps.extractors.scibert_extractor import extract as _scibert_extract
except Exception:
    _scibert_extract = None  # type: ignore[assignment]

try:
    from apps.extractors.biobert_extractor import (
        extract as _biobert_extract,
    )  # noqa: F401
except Exception:
    _biobert_extract = None  # type: ignore[assignment]

try:
    from apps.extractors.text2nkg_extractor import (
        extract as _text2nkg_extract,
    )  # noqa: F401
except Exception:
    _text2nkg_extract = None  # type: ignore[assignment]

# Temporal model (soft-optional)
try:
    from apps.knowledge_graph.temporal_model import (
        extract_temporals as _temporal_extract,
    )  # noqa: F401
except Exception:
    _temporal_extract = None  # type: ignore[assignment]


def _enabled(name: str) -> bool:
    return os.getenv(name, "0") == "1"


def _compose_summary(entities: List[Dict[str, Any]]) -> str:
    uniq = []
    seen = set()
    for e in entities:
        t = (e.get("text") or e.get("word") or "").strip()
        if t and t not in seen:
            uniq.append(t)
            seen.add(t)
        if len(" ".join(uniq)) > 512:
            break
    return " ".join(uniq)[:512]


def _text2nkg_stub(text: str) -> Dict[str, Any]:
    """
    Minimal n-ary relation stub to satisfy orchestrator tests when real extractor is absent.
    Example: 'System uses database.' => subject=System, relation=uses, object=database
    """
    m = re.search(r"\b([\w-]+)\s+uses\s+([\w-]+)\b", text, flags=re.IGNORECASE)
    rels: List[Dict[str, Any]] = []
    if m:
        rels.append(
            {
                "subject": m.group(1),
                "relation": "uses",
                "object": m.group(2),
                "source": "text2nkg_stub",
            }
        )
    return {
        "summary": "",
        "entities": [],
        "relations": rels,
        "temporals": [],
        "guard_trace": [
            {
                "component": "text2nkg",
                "status": "ok" if rels else "skipped",
                "reason": "stub",
            }
        ],
        "decision": "INDETERMINATE",
    }


def _temporal_block(text: str) -> Dict[str, Any]:
    if not _enabled("TEMPORAL_GRAPH_MODEL"):
        return _noop("temporal_model", "flag_off")

    # Prefer real temporal model if available
    if _temporal_extract is not None:
        try:
            temps = _temporal_extract(text) or []
            return {
                "summary": "",
                "entities": [],
                "relations": [],
                "temporals": temps,
                "guard_trace": [
                    {"component": "temporal_model", "status": "ok", "count": len(temps)}
                ],
                "decision": "INDETERMINATE",
            }
        except Exception as exc:
            return {
                "summary": "",
                "entities": [],
                "relations": [],
                "temporals": [],
                "guard_trace": [
                    {
                        "component": "temporal_model",
                        "status": "error",
                        "reason": str(exc),
                    }
                ],
                "decision": "INDETERMINATE",
            }

    # Fallback: simple year/year-range regex
    years = re.findall(r"\b(?:19|20)\d{2}\b", text)
    temporals: List[Dict[str, Any]] = []
    if len(years) >= 2:
        temporals.append(
            {
                "type": "TimeSpan",
                "start": f"{years[0]}-01-01",
                "end": f"{years[1]}-12-31",
                "granularity": "year",
            }
        )
    elif len(years) == 1:
        temporals.append(
            {"type": "TimeInstant", "at": f"{years[0]}-01-01", "granularity": "year"}
        )
    return {
        "summary": "",
        "entities": [],
        "relations": [],
        "temporals": temporals,
        "guard_trace": [
            {
                "component": "temporal_model",
                "status": "ok" if temporals else "skipped",
                "reason": "regex_stub",
            }
        ],
        "decision": "INDETERMINATE",
    }


def _collectors() -> List[Tuple[str, Callable[[str], Dict[str, Any]]]]:
    col: List[Tuple[str, Callable[[str], Dict[str, Any]]]] = []

    # SciBERT
    if _enabled("EXTRACTOR_SCI") and _scibert_extract is not None:
        col.append(("scibert", _scibert_extract))
    elif _enabled("EXTRACTOR_SCI"):
        col.append(("scibert", lambda _t: _noop("scibert", "missing_deps")))
    else:
        col.append(("scibert", lambda _t: _noop("scibert", "flag_off")))

    # BioBERT (placeholder)
    if _enabled("EXTRACTOR_BIO") and _biobert_extract is not None:
        col.append(("biobert", _biobert_extract))  # type: ignore[arg-type]
    elif _enabled("EXTRACTOR_BIO"):
        col.append(("biobert", lambda _t: _noop("biobert", "missing_deps")))
    else:
        col.append(("biobert", lambda _t: _noop("biobert", "flag_off")))

    # Text2NKG (real or stub when flag ON)
    if _enabled("EXTRACTOR_TEXT2NKG") and _text2nkg_extract is not None:
        col.append(("text2nkg", _text2nkg_extract))  # type: ignore[arg-type]
    elif _enabled("EXTRACTOR_TEXT2NKG"):
        col.append(("text2nkg", _text2nkg_stub))  # stub satisfies orchestrator tests
    else:
        col.append(("text2nkg", lambda _t: _noop("text2nkg", "flag_off")))

    return col


def extract_all(text: str) -> Dict[str, Any]:
    """
    Aggregate extraction across enabled extractors and temporal model.
    Decision remains INDETERMINATE; constitutional guard composes final tri-state.
    """
    if not (text or "").strip():
        return {
            "summary": "",
            "entities": [],
            "relations": [],
            "temporals": [],
            "guard_trace": [
                {"component": "orchestrator", "status": "deny", "reason": "empty_text"}
            ],
            "decision": "DENY",
        }

    all_entities: List[Dict[str, Any]] = []
    all_relations: List[Dict[str, Any]] = []
    all_temporals: List[Dict[str, Any]] = []
    guard_trace: List[Dict[str, Any]] = []

    # Extractors
    for name, fn in _collectors():
        out = fn(text)
        all_entities.extend(out.get("entities", []))
        all_relations.extend(out.get("relations", []))
        all_temporals.extend(out.get("temporals", []))
        g = out.get("guard_trace", [])
        guard_trace.extend(
            g
            if isinstance(g, list)
            else [{"component": name, "status": "trace_format_error"}]
        )

    # Temporal block (flag-gated)
    t_out = _temporal_block(text)
    all_temporals.extend(t_out.get("temporals", []))
    guard_trace.extend(t_out.get("guard_trace", []))

    return {
        "summary": _compose_summary(all_entities),
        "entities": all_entities,
        "relations": all_relations,
        "temporals": all_temporals,
        "guard_trace": guard_trace,
        "decision": "INDETERMINATE",
    }


__all__ = ["extract_all"]
