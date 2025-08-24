# SPDX-License-Identifier: MIT
from __future__ import annotations
import importlib
import os
import time
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Dict, Optional, List

from .doc_biaso import load_doc_biaso_ontology

# In-memory stub store for tests
_STUB_EVENTS: List[Dict[str, Any]] = []


def get_stub_events() -> List[Dict[str, Any]]:
    return list(_STUB_EVENTS)


@dataclass
class BiasLogger:
    mode: str = "stub"  # "stub" | "neo4j"

    def log_annotation(
        self, *, document_id: Optional[str], annotation: Dict[str, Any]
    ) -> None:
        if self.mode == "neo4j":
            self._log_neo4j(document_id=document_id, annotation=annotation)
        else:
            self._log_stub(document_id=document_id, annotation=annotation)

    def _log_stub(
        self, *, document_id: Optional[str], annotation: Dict[str, Any]
    ) -> None:
        evt = {
            "ts": int(time.time() * 1000),
            "document_id": document_id,
            "annotation": annotation,
        }
        _STUB_EVENTS.append(evt)
        base = os.getenv("PROV_PATH", "var/provenance")
        Path(base).mkdir(parents=True, exist_ok=True)
        p = Path(base) / time.strftime("bias-prov-%Y%m%d.jsonl", time.gmtime())
        with p.open("a", encoding="utf-8") as f:
            f.write(json.dumps(evt, ensure_ascii=False) + "\n")

    def _log_neo4j(
        self, *, document_id: Optional[str], annotation: Dict[str, Any]
    ) -> None:
        try:
            mod = importlib.import_module("apps.provenance.neo4j_write")
        except Exception:
            self._log_stub(document_id=document_id, annotation=annotation)
            return
        writer = getattr(mod, "Neo4jProvenanceWriter", None)
        if writer is None:
            self._log_stub(document_id=document_id, annotation=annotation)
            return
        try:
            w = writer()  # default ctor or DI elsewhere
            fn = getattr(w, "log_bias_transformation_with_ontology", None) or getattr(
                w, "log_event", None
            )
            if fn is None:
                self._log_stub(document_id=document_id, annotation=annotation)
                return
            payload = {
                "type": "bias_annotation",
                "document_id": document_id,
                "annotation": annotation,
            }
            if fn.__name__ == "log_event":
                fn("bias_annotation", payload)
            else:
                fn(
                    input_anchor=annotation.get("segment_anchor"),
                    output_anchor=annotation.get("segment_anchor"),
                    bias_annotation=annotation,
                )
        except Exception:
            self._log_stub(document_id=document_id, annotation=annotation)


def get_bias_logger() -> BiasLogger:
    mode = os.getenv("CBDT_PROV_MODE", "").strip().lower()
    if os.getenv("CBDT_PROVENANCE", "").strip().lower() not in {"1", "true", "yes"}:
        return BiasLogger(mode="stub")  # provenance effectively off
    return BiasLogger(mode="neo4j" if mode == "neo4j" else "stub")


def make_bias_annotation(
    *,
    segment_anchor: Optional[dict],
    scores: Dict[str, float],
    flags: Dict[str, float],
    backend: str,
    threshold: float,
) -> Dict[str, Any]:
    from datetime import datetime
    import uuid

    dbo = load_doc_biaso_ontology()
    top_key = max(scores.items(), key=lambda kv: kv[1])[0] if scores else "unknown"
    return {
        "id": "bias_annotation_" + str(uuid.uuid4()),
        "segment_anchor": segment_anchor,
        "ontology_classification": dbo.classify_bias_type(top_key),
        "scores": scores,
        "flags": flags,
        "detector_backend": backend,
        "threshold": threshold,
        "timestamp": datetime.utcnow().isoformat() + "Z",
        "ontology_version": dbo.version,
    }
