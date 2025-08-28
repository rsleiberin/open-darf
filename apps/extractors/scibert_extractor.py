from __future__ import annotations
import os
from typing import Any, Dict, List

# Soft-optional deps: module must import even if transformers is absent
_AVAILABLE = True
try:
    from transformers import pipeline  # type: ignore
except Exception:  # pragma: no cover
    _AVAILABLE = False

_NER = None  # lazy HF pipeline


def _allow_load() -> bool:
    return os.getenv("EXTRACTOR_SCI", "0") == "1"


def _ner_model_id() -> str:
    # Override to a SciBERT fine-tune when available
    return os.getenv("SCIBERT_NER_MODEL_ID", "dslim/bert-base-NER")


def _load() -> None:
    global _NER
    if _NER is not None:
        return
    if not _AVAILABLE:
        raise RuntimeError("SciBERT extractor unavailable: missing transformers")
    _NER = pipeline("ner", model=_ner_model_id(), aggregation_strategy="simple")


def extract(text: str) -> Dict[str, Any]:
    guard_trace: List[Dict[str, Any]] = []

    if not _allow_load():
        guard_trace.append(
            {"component": "scibert", "status": "skipped", "reason": "flag_off"}
        )
        return {
            "summary": "",
            "entities": [],
            "relations": [],
            "temporals": [],
            "guard_trace": guard_trace,
            "decision": "INDETERMINATE",
        }

    if not _AVAILABLE:
        guard_trace.append(
            {"component": "scibert", "status": "unavailable", "reason": "missing_deps"}
        )
        return {
            "summary": "",
            "entities": [],
            "relations": [],
            "temporals": [],
            "guard_trace": guard_trace,
            "decision": "INDETERMINATE",
            "error": "missing_dependencies",
        }

    try:
        _load()
        assert _NER is not None
        raw = _NER(text)
        entities = [
            {
                "text": e.get("word"),
                "label": e.get("entity_group"),
                "start": int(e.get("start", -1)),
                "end": int(e.get("end", -1)),
                "score": float(e.get("score", 0.0)),
                "source": "scibert_ner",
            }
            for e in raw
        ]
        guard_trace.append(
            {"component": "scibert", "status": "ok", "count": len(entities)}
        )
        return {
            "summary": " ".join(sorted({e["text"] for e in entities}))[:512],
            "entities": entities,
            "relations": [],
            "temporals": [],
            "guard_trace": guard_trace,
            "decision": "INDETERMINATE",
        }
    except Exception as exc:  # pragma: no cover
        guard_trace.append(
            {"component": "scibert", "status": "error", "reason": str(exc)}
        )
        return {
            "summary": "",
            "entities": [],
            "relations": [],
            "temporals": [],
            "guard_trace": guard_trace,
            "decision": "INDETERMINATE",
            "error": "runtime_error",
        }


class SciBERTExtractor:
    """Class shim for legacy imports. Safe when deps missing and flag is OFF."""

    name = "scibert"

    def extract(self, text: str) -> Dict[str, Any]:
        return extract(text)

    def __call__(self, text: str) -> Dict[str, Any]:
        return self.extract(text)


__all__ = ["extract", "SciBERTExtractor"]
