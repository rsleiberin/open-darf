from __future__ import annotations
from dataclasses import dataclass, asdict
from typing import Dict, Any, Optional, List
import os
import json
import time
from pathlib import Path
import datetime as _dt


@dataclass
class OscarResult:
    doc_id: str
    version: str
    risk_score: float  # 0.0 .. 1.0
    tags: List[str]
    timing_ms: float
    receipt_path: Optional[str] = None


def _on(k: str) -> bool:
    return str(os.getenv(k, "")).strip().lower() in {"1", "true", "yes", "on"}


def _safe_write(path: str, payload: Dict[str, Any]) -> None:
    try:
        p = Path(path)
        p.parent.mkdir(parents=True, exist_ok=True)
        with open(p, "w", encoding="utf-8") as f:
            json.dump(payload, f, ensure_ascii=False, indent=2)
    except Exception:
        pass  # never throws


_WORDS = {
    "loaded_language": ["clearly", "undeniable", "obviously", "certainly"],
    "hedging": ["might", "could", "perhaps", "suggests", "appears"],
    "appeal_to_authority": ["experts say", "studies show"],
}


def oscar_pass(ctx: Dict[str, Any], doc: Dict[str, Any]) -> OscarResult:
    """
    OSCaR (Outcome Scorecard & Rationale) — flag-gated, lightweight signaler.
    - Off by default; enable with PIPELINE_OSCAR=1
    - Deterministic, PR-safe (no network)
    - Writes receipts iff PIPELINE_PERF=1
    """
    doc_id = str(doc.get("doc_id", "unknown"))
    if not _on("PIPELINE_OSCAR"):
        return OscarResult(
            doc_id=doc_id,
            version="0",
            risk_score=0.0,
            tags=[],
            timing_ms=0.0,
            receipt_path=None,
        )

    t0 = time.perf_counter()
    # Extract a simple text surface from doc structure
    text = ""
    blocks = doc.get("blocks") or []
    if isinstance(blocks, list) and blocks and isinstance(blocks[0], dict):
        text = blocks[0].get("text") or ""
    else:
        text = doc.get("text", "") or ""

    tl = text.lower()
    hits = []
    for label, words in _WORDS.items():
        for w in words:
            if w in tl:
                hits.append(label)

    # Simple deterministic risk scoring (bounded)
    unique_labels = sorted(set(hits))
    risk = min(1.0, len(unique_labels) / 3.0)

    elapsed = (time.perf_counter() - t0) * 1000.0
    res = OscarResult(
        doc_id=doc_id,
        version="0",
        risk_score=risk,
        tags=unique_labels,
        timing_ms=elapsed,
        receipt_path=None,
    )

    if _on("PIPELINE_PERF"):
        ts = _dt.datetime.utcnow().strftime("%Y%m%d-%H%M%S")
        d1 = Path(f"docs/audit/pipeline/pipeline_oscar/{ts}")
        d1.mkdir(parents=True, exist_ok=True)
        d2 = Path("docs/audit/pipeline/pipeline_oscar/_last")
        d2.mkdir(parents=True, exist_ok=True)
        payload = asdict(res)
        path1 = d1 / f"{doc_id}.json"
        path2 = d2 / f"{doc_id}.json"
        _safe_write(str(path1), payload)
        _safe_write(str(path2), payload)
        res.receipt_path = str(path1)

    return res
