"""
CBDT (Contextualized Bi-Directional Dual Transformer) — pipeline pass (flag-gated).

Phase 3 / Task A goals:
- Off by default; enable via PIPELINE_CBDT=1
- Lazy provider initialization (no top-level heavy deps)
- Deterministic unit-test mode; fast PR path via NullCBDT
- Observability never throws; receipts are append-only and compact
"""

from __future__ import annotations

import json
import os
import time
from dataclasses import dataclass, asdict
from pathlib import Path
from typing import Dict, List, Optional, Tuple, Any

# ---------------------- Public contracts ---------------------------------------------------------

LABELS: Tuple[str, ...] = (
    "loaded_language",
    "appeal_to_authority",
    "ad_hominem",
    "hyperbole",
    "hedging",
    "weasel_words",
    "selection_bias",
    "framing",
)


@dataclass
class Block:
    id: str
    text: str
    order: Optional[int] = None
    anchor_ref: Optional[str] = None


@dataclass
class DocIn:
    doc_id: str
    blocks: List[Block]
    lang: Optional[str] = None
    mime: Optional[str] = None
    source_uri: Optional[str] = None


@dataclass
class Finding:
    block_id: str
    label: str
    score: float
    cues: List[str]
    span: Optional[Tuple[int, int]] = None


@dataclass
class CBDTResult:
    findings: List[Finding]
    summary: Dict[str, Any]


# ---------------------- Provider interface -------------------------------------------------------


class CBDTProvider:
    """Interface for CBDT providers."""

    name = "abstract"
    version = "0.0.0"

    def score(self, doc: DocIn) -> CBDTResult:  # pragma: no cover
        raise NotImplementedError


class NullCBDT(CBDTProvider):
    """Fast no-op provider for PR CI and disabled environments."""

    name = "NullCBDT"
    version = "1.0.0"

    def score(self, doc: DocIn) -> CBDTResult:
        return CBDTResult(findings=[], summary=_mk_summary([], self))


class LocalCBDT(CBDTProvider):
    """
    Lightweight heuristic stand-in for a real CBDT model.
    Deterministic and fast; no heavyweight deps.
    """

    name = "LocalCBDT-heuristic"
    version = "0.1.0"
    _cue_map: Dict[str, Tuple[str, ...]] = {
        "loaded_language": ("clearly", "undeniable", "obviously"),
        "appeal_to_authority": ("experts say", "studies show"),
        "ad_hominem": ("idiot", "fool", "incompetent"),
        "hyperbole": ("always", "never", "everyone knows"),
        "hedging": ("might", "could", "perhaps", "suggests"),
        "weasel_words": ("some say", "people are saying"),
        "selection_bias": ("handpicked", "cherry-picked"),
        "framing": ("despite", "even though"),
    }

    def score(self, doc: DocIn) -> CBDTResult:
        findings: List[Finding] = []
        for b in doc.blocks:
            text_l = (b.text or "").lower()
            for label, cues in self._cue_map.items():
                hit_cues = [c for c in cues if c in text_l]
                if hit_cues:
                    base = min(0.98, max(0.5, 0.6 + 0.1 * len(hit_cues)))  # clamp
                    findings.append(
                        Finding(
                            block_id=b.id,
                            label=label,
                            score=base,
                            cues=hit_cues,
                            span=None,
                        )
                    )
        return CBDTResult(findings=findings, summary=_mk_summary(findings, self))


# ---------------------- Public pass --------------------------------------------------------------


def cbdt_pass(ctx: Optional[Dict[str, Any]], doc: Dict[str, Any]) -> CBDTResult:
    """
    Run CBDT over a parsed document. Flag-gated via PIPELINE_CBDT.
    Writes receipts if PIPELINE_PERF is on. Observability never throws.
    """
    if not _flag_on("PIPELINE_CBDT"):
        provider = NullCBDT()
        res = provider.score(_as_docin(doc))
        return res

    t0 = time.perf_counter()
    provider = _select_provider(os.getenv("PIPELINE_CBDT_PROVIDER", "null"))
    docin = _as_docin(doc)
    res = provider.score(docin)
    elapsed_ms = (time.perf_counter() - t0) * 1000.0

    # Observability counters (never throws)
    try:
        from apps import obs as _obs

        _obs.increment("cbdt.runs", 1)
        _obs.increment("cbdt.findings_total", len(res.findings))
        # per-label counts
        for lb, cnt in res.summary.get("counts_by_label", {}).items():
            _obs.increment(f"cbdt.counts.{lb}", cnt)
        _obs.histogram("cbdt.ms", elapsed_ms)
    except Exception:
        # never throw; defer to summary signals if needed
        pass

    obs_error = None
    try:
        if _flag_on("PIPELINE_PERF"):
            receipt = _build_receipt(
                doc_id=docin.doc_id,
                provider=provider,
                findings=res.findings,
                elapsed_ms=elapsed_ms,
                blocks_scored=len(docin.blocks),
            )
            _safe_write_json(
                receipt["__path__"],
                {k: v for k, v in receipt.items() if k != "__path__"},
            )
            _last_dir = Path("docs/audit/pipeline/pipeline_cbdt/_last")
            _last_dir.mkdir(parents=True, exist_ok=True)
            _last_path = _last_dir / f"{docin.doc_id}.json"
            _safe_write_json(
                str(_last_path), {k: v for k, v in receipt.items() if k != "__path__"}
            )
            # Expose for tests/tools
            res.summary["receipt_path"] = receipt["__path__"]
            res.summary["receipt_last"] = str(_last_path)
    except Exception as e:  # pragma: no cover
        obs_error = type(e).__name__

    res.summary.setdefault("timing_ms", {})
    res.summary["timing_ms"].setdefault("cbdt_total", elapsed_ms)
    res.summary.setdefault("signals", [])
    res.summary["signals"].append(f"obs_error:{obs_error or 'none'}")
    return res


# ---------------------- Internals ----------------------------------------------------------------


def _flag_on(key: str) -> bool:
    return os.getenv(key, "").strip().lower() not in ("", "0", "false", "off")


def _as_docin(doc: Dict[str, Any]) -> DocIn:
    blocks = [
        Block(**b) if not isinstance(b, Block) else b for b in doc.get("blocks", [])
    ]
    return DocIn(
        doc_id=str(doc.get("doc_id", "unknown")),
        blocks=blocks,
        lang=doc.get("lang"),
        mime=doc.get("mime"),
        source_uri=doc.get("source_uri"),
    )


def _select_provider(kind: str) -> CBDTProvider:
    k = (kind or "null").lower()
    if k == "local":
        return LocalCBDT()
    return NullCBDT()


def _mk_summary(findings: List[Finding], provider: CBDTProvider) -> Dict[str, Any]:
    counts: Dict[str, int] = {}
    for f in findings:
        counts[f.label] = counts.get(f.label, 0) + 1
    top_cues: List[str] = []
    for f in findings:
        for c in f.cues:
            if c not in top_cues:
                top_cues.append(c)
    return {
        "counts_by_label": counts,
        "findings_total": len(findings),
        "top_cues": top_cues[:10],
        "model": {"name": provider.name, "version": provider.version},
    }


def _build_receipt(
    doc_id: str,
    provider: CBDTProvider,
    findings: List[Finding],
    elapsed_ms: float,
    blocks_scored: Optional[int] = None,
) -> Dict[str, Any]:
    ts = time.strftime("%Y%m%d-%H%M%S")
    outdir = Path("docs/audit/pipeline/pipeline_cbdt") / ts
    outdir.mkdir(parents=True, exist_ok=True)
    # Build counters without dict union (Py 3.8-safe)
    counters = _mk_summary(findings, provider)
    if blocks_scored is not None:
        counters = dict(counters)  # shallow copy
        counters["blocks_scored"] = blocks_scored
    receipt = {
        "pipeline_run_id": _safe_uuid(),
        "doc_id": doc_id,
        "flags": {"PIPELINE_CBDT": True, "PIPELINE_PERF": _flag_on("PIPELINE_PERF")},
        "timing_ms": {
            "cbdt_total": round(elapsed_ms, 3),
            "p50": round(elapsed_ms, 3),
            "p95": round(elapsed_ms, 3),
            "max": round(elapsed_ms, 3),
        },
        "counters": counters,
        "model": {
            "name": provider.name,
            "version": provider.version,
            "provider": provider.name,
        },
        "signals": [],
        "findings_sample": [asdict(findings[0])] if findings else [],
    }
    receipt["__path__"] = str(outdir / f"{doc_id}.json")
    return receipt


def _safe_write_json(path: str, payload: Dict[str, Any]) -> None:
    try:
        with open(path, "w", encoding="utf-8") as f:
            json.dump(payload, f, ensure_ascii=False, indent=2)
    except Exception:
        pass  # observability must never throw


def _safe_uuid() -> str:
    import os as _os
    import time as _time
    import random as _random

    return f"{int(_time.time()*1000):x}-{_os.getpid():x}-{_random.getrandbits(64):x}"


__all__ = [
    "cbdt_pass",
    "CBDTProvider",
    "NullCBDT",
    "LocalCBDT",
    "CBDTResult",
    "Finding",
    "LABELS",
]
