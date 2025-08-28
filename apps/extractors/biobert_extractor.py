from __future__ import annotations
import os
from typing import Any, Dict, List, Optional

# Soft-optional dependency
_AVAILABLE = True
try:
    from transformers import pipeline  # type: ignore
except Exception:  # pragma: no cover
    _AVAILABLE = False

_NER = None  # lazy pipeline


def _allow_load() -> bool:
    return os.getenv("EXTRACTOR_BIO", "0") == "1"


def _ner_model_id() -> str:
    # Default to a general biomedical NER; override via env if desired
    return os.getenv("BIOBERT_NER_MODEL_ID", "d4data/biomedical-ner-all")


def _load() -> None:
    global _NER
    if _NER is None and _AVAILABLE:
        try:
            _NER = pipeline(  # type: ignore
                "token-classification",
                model=_ner_model_id(),
                aggregation_strategy="simple",
            )
        except Exception:
            _NER = None  # remain safe if model unavailable


def _neutral(reason: str, decision: str = "INDETERMINATE") -> Dict[str, Any]:
    return {
        "summary": "",
        "entities": [],
        "relations": [],
        "temporals": [],
        "guard_trace": [
            {"component": "biobert", "status": "skipped", "reason": reason}
        ],
        "reason_code": reason,
        "decision": decision,
    }


def extract(text: str) -> Dict[str, Any]:
    # 1) Empty text DENY (before any heavy deps) to satisfy tests and guards
    if not (text or "").strip():
        return _neutral("empty_text", decision="DENY")

    # 2) Flag OFF -> neutral skip with explicit reason_code
    if not _allow_load():
        return _neutral("disabled")

    # 3) Missing deps -> neutral skip
    if not _AVAILABLE:
        return _neutral("missing_deps")

    # 4) Try to run the pipeline lazily
    _load()
    if _NER is None:
        return _neutral("pipeline_unavailable")

    spans = _NER(text)  # type: ignore
    ents: List[Dict[str, Any]] = []
    for s in spans or []:
        ents.append(
            {
                "text": s.get("word") or s.get("entity_group") or "",
                "label": s.get("entity_group") or s.get("entity") or "ENT",
                "start": int(s.get("start", -1)),
                "end": int(s.get("end", -1)),
                "score": float(s.get("score", 0.0)),
                "source": "biobert",
            }
        )
    return {
        "summary": f"{len(ents)} biomedical entities" if ents else "",
        "entities": ents,
        "relations": [],
        "temporals": [],
        "guard_trace": [{"component": "biobert", "status": "ran", "reason": "ok"}],
        "reason_code": "ok" if ents else "no_entities",
        "decision": "INDETERMINATE",
    }


class BioBERTExtractor:
    """Compatibility shim matching test expectations."""

    def __init__(self, model_id: Optional[str] = None) -> None:
        if model_id:
            os.environ.setdefault("BIOBERT_NER_MODEL_ID", model_id)

    def __call__(self, text: str) -> Dict[str, Any]:
        return extract(text)

    def extract(self, text: str) -> Dict[str, Any]:
        return extract(text)

    @staticmethod
    def extract_static(text: str) -> Dict[str, Any]:
        return extract(text)


__all__ = ["BioBERTExtractor", "extract"]
