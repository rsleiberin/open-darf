from __future__ import annotations
from typing import Dict, Any, Optional
import os
import json
import time
import datetime as _dt
from dataclasses import dataclass
from pathlib import Path


@dataclass
class ProvResult:
    doc_id: str
    jsonld: Dict[str, Any]
    timing_ms: float
    receipt_path: Optional[str] = None


def _on(k: str) -> bool:
    return str(os.getenv(k, "")).strip().lower() in {"1", "true", "yes", "on"}


def _iso(ts: float) -> str:
    return (
        _dt.datetime.utcfromtimestamp(ts).replace(tzinfo=_dt.timezone.utc).isoformat()
    )


def _safe_write(path: str, payload: Dict[str, Any]) -> None:
    try:
        p = Path(path)
        p.parent.mkdir(parents=True, exist_ok=True)
        with open(p, "w", encoding="utf-8") as f:
            json.dump(payload, f, ensure_ascii=False, indent=2)
    except Exception:
        pass  # never throw


def prov_pass(ctx: Dict[str, Any], doc: Dict[str, Any]) -> ProvResult:
    """
    Build a compact PROV-O JSON-LD bundle for a single document.
    Off by default; enable with PIPELINE_PROV=1. Writes a per-doc receipt when PIPELINE_PERF=1.
    """
    if not _on("PIPELINE_PROV"):
        return ProvResult(
            doc_id=str(doc.get("doc_id", "unknown")),
            jsonld={},
            timing_ms=0.0,
            receipt_path=None,
        )

    t0 = time.perf_counter()
    doc_id = str(doc.get("doc_id", "unknown"))
    now = time.time()

    ent_id = f"urn:doc:{doc_id}"
    act_id = "urn:activity:pipeline-run_once"
    ag_id = "urn:agent:pipeline"

    jsonld = {
        "@context": "https://www.w3.org/ns/prov#",
        "entity": {"@id": ent_id, "prov:type": "prov:Entity"},
        "activity": {
            "@id": act_id,
            "prov:type": "prov:Activity",
            "prov:startedAtTime": _iso(now),
            "prov:endedAtTime": _iso(now),  # same tick; we don't long-run here
        },
        "agent": {"@id": ag_id, "prov:type": "prov:SoftwareAgent"},
        "wasGeneratedBy": {"prov:entity": ent_id, "prov:activity": act_id},
        "wasAssociatedWith": {"prov:activity": act_id, "prov:agent": ag_id},
    }

    elapsed_ms = (time.perf_counter() - t0) * 1000.0
    res = ProvResult(
        doc_id=doc_id, jsonld=jsonld, timing_ms=elapsed_ms, receipt_path=None
    )

    if _on("PIPELINE_PERF"):
        # Append-only receipt under timestamped dir and stable _last mirror
        ts = _dt.datetime.utcnow().strftime("%Y%m%d-%H%M%S")
        receipt_dir = Path(f"docs/audit/pipeline/pipeline_prov/{ts}")
        stable_dir = Path("docs/audit/pipeline/pipeline_prov/_last")
        payload = {
            "doc_id": doc_id,
            "jsonld": jsonld,
            "timing_ms": elapsed_ms,
            "flags": {"PIPELINE_PROV": True, "PIPELINE_PERF": True},
        }
        path1 = receipt_dir / f"{doc_id}.json"
        path2 = stable_dir / f"{doc_id}.json"
        _safe_write(str(path1), payload)
        _safe_write(str(path2), payload)
        res.receipt_path = str(path1)
    return res
