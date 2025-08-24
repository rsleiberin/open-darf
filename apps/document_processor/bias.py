# SPDX-License-Identifier: MIT
"""
Bias detection pipeline entrypoint.

- classify_text(): uses CBDTBiasDetector with env-selected backend (default tiny).
  * Emits a receipt via apps.api.receipts.emit() when available; otherwise falls
    back to a local JSONL writer under RECEIPTS_PATH (or var/receipts).
  * Optionally logs a provenance annotation (Doc-BiasO) via DI-friendly logger.
  * Optional OSCaR neutralization with a semantic fidelity gate (default 0.95).
"""
from __future__ import annotations

import importlib
import json
import os
import time
from pathlib import Path
from typing import Any, Dict, Iterable, Mapping, Optional

from apps.document_processor.cbdt import CBDTBiasDetector, CBDTConfig
from apps.document_processor.cbdt.adapters import get_models_from_env
from apps.provenance.bias_logger import get_bias_logger, make_bias_annotation
from apps.document_processor.oscar.pipeline import neutralize_text_for_flags


def _try_get_receipts_module():
    try:
        return importlib.import_module("apps.api.receipts")
    except Exception:
        return None


def _fallback_write_receipt(payload: Dict[str, Any]) -> Optional[str]:
    """Local JSONL fallback writer used when receipts.emit() is unavailable."""
    base = os.getenv("RECEIPTS_PATH", "var/receipts")
    Path(base).mkdir(parents=True, exist_ok=True)
    fname = time.strftime("cbdt-%Y%m%d.jsonl", time.gmtime())
    path = Path(base) / fname
    try:
        with path.open("a", encoding="utf-8") as f:
            f.write(json.dumps(payload, ensure_ascii=False) + "\n")
        return str(path)
    except Exception:
        return None


def classify_text(
    text: str,
    *,
    citations: Optional[Iterable[str]] = None,
    metadata: Optional[Mapping[str, Any]] = None,
    threshold: Optional[float] = None,
    doc_id: Optional[str] = None,
    segment_anchor: Optional[dict] = None,
    neutralize: bool = False,
    min_fidelity: float = 0.95,
    emit_receipt: bool = True,
) -> Dict[str, Any]:
    """
    Returns:
      {
        "scores": {...},
        "flags": {...},
        "backend": "<backend version tag>",
        "receipt_path": "<file or None>",
        "neutralizations": <dict or None>
      }
    """
    # --- CBDT detection ---
    cm, xm, fusion, version = get_models_from_env()
    cfg = CBDTConfig(threshold=threshold if threshold is not None else 0.5)
    det = CBDTBiasDetector(
        content_model=cm, context_model=xm, fusion=fusion, config=cfg
    )

    t0 = time.time()
    result = det.classify(text, citations=citations, metadata=metadata)
    latency_ms = int((time.time() - t0) * 1000)

    # --- OSCaR neutralization (optional) ---
    neutralizations = None
    if neutralize:
        try:
            osc = neutralize_text_for_flags(
                text, result["flags"], min_fidelity=min_fidelity
            )
            neutralizations = osc
        except Exception:
            neutralizations = {"text": text, "changes": [], "human_review": True}

    # --- receipts (best-effort) ---
    receipt_path: Optional[str] = None
    if emit_receipt:
        payload = {
            "component": "cbdt_bias",
            "backend": version,
            "threshold": cfg.threshold,
            "scores": result["scores"],
            "flags": result["flags"],
            "latency_ms": latency_ms,
            "neutralizations": neutralizations,
        }
        receipts = _try_get_receipts_module()
        if receipts is not None:
            try:
                receipt_path = receipts.emit(payload, t0=t0)
            except Exception:
                receipt_path = None
        if not receipt_path:
            receipt_path = _fallback_write_receipt(payload)

    # --- provenance (optional via env) ---
    try:
        if os.getenv("CBDT_PROVENANCE", "").strip().lower() in {"1", "true", "yes"}:
            logger = get_bias_logger()
            ann = make_bias_annotation(
                segment_anchor=segment_anchor,
                scores=result["scores"],
                flags=result["flags"],
                backend=version,
                threshold=cfg.threshold,
            )
            logger.log_annotation(document_id=doc_id, annotation=ann)
    except Exception:
        # Never let provenance break classification
        pass

    return {
        **result,
        "backend": version,
        "receipt_path": receipt_path,
        "neutralizations": neutralizations,
    }


# ---- Backward-compat shims (Phase-1 API) ------------------------------------
def score_bias(text: str):
    """
    Legacy helper returning an object with:
      .label ('flag'|'ok'), .score (float), .reasons (list[str]),
      plus .scores and .flags dicts.
    Uses CBDT classify_text() and an assertive-language heuristic.
    Adds reason tags "absolutes" and/or "intensifiers" for legacy tests.
    """
    from types import SimpleNamespace
    import re as _re

    ABSOLUTES = {"always", "never", "guaranteed", "perfect"}
    INTENSIFIERS = {"clearly", "best"}

    def _token_set(t: str):
        return set(_re.sub(r"[^a-z0-9]+", " ", t.lower()).split())

    toks = _token_set(text)
    has_abs = bool(ABSOLUTES & toks)
    has_int = bool(INTENSIFIERS & toks)
    has_assertive = has_abs or has_int

    out = classify_text(text, emit_receipt=False)
    flags = out.get("flags", {})
    scores = out.get("scores", {})

    max_score = max(scores.values()) if scores else 0.0

    # Label: flagged if any category flagged OR assertive terms present.
    label = "flag" if any(v > 0 for v in flags.values()) or has_assertive else "ok"

    # Legacy .score: take max score; if assertive triggered and max < 0.5, bump to 0.5
    score = max_score
    if has_assertive and score < 0.5:
        score = 0.5

    # Reasons: top scores + reason tags expected by legacy tests
    top = sorted(scores.items(), key=lambda kv: (-kv[1], kv[0]))
    reasons = [f"{k}={v:.2f}" for k, v in top[:3]] or []
    if has_abs:
        reasons.append("absolutes")
    if has_int:
        reasons.append("intensifiers")
    if not reasons:
        reasons = ["no-salient-reason"]

    return SimpleNamespace(
        label=label, score=score, reasons=reasons, scores=scores, flags=flags
    )


def filter_segments(text_or_segments, threshold: float = 0.5, categories=None):
    """
    Legacy helper:
      - If given a LIST/TUPLE of segments -> returns:
          {
            "kept_count", "removed_count",
            "kept_indices", "removed_indices",
            "kept": List[Tuple[int, str]],
            "removed": List[Tuple[int, str, str]],  # (index, segment, "flag")
          }
      - If given a single string -> returns the flags dict (optionally filtered).
    Mirrors Phase-1 assertive-terms heuristic ("clearly","always","never","best","guaranteed","perfect").
    """
    import re as _re

    def _has_assertive(t: str) -> bool:
        norm = " " + _re.sub(r"[^a-z0-9]+", " ", t.lower()) + " "
        for w in ("clearly", "always", "never", "best", "guaranteed", "perfect"):
            if f" {w} " in norm:
                return True
        return False

    # list/tuple path -> counts + indices + (index,segment)/(index,segment,"flag")
    if isinstance(text_or_segments, (list, tuple)):
        kept_indices, removed_indices = [], []
        kept, removed = [], []
        cats = set(categories) if categories else None

        for i, seg in enumerate(text_or_segments):
            out = classify_text(seg, threshold=threshold, emit_receipt=False)
            f = out.get("flags", {})
            if cats is not None:
                f = {k: v for k, v in f.items() if k in cats}
            flagged = any(v > 0 for v in f.values()) or _has_assertive(seg)
            if flagged:
                removed_indices.append(i)
                removed.append((i, seg, "flag"))
            else:
                kept_indices.append(i)
                kept.append((i, seg))
        return {
            "kept_count": len(kept_indices),
            "removed_count": len(removed_indices),
            "kept_indices": kept_indices,
            "removed_indices": removed_indices,
            "kept": kept,
            "removed": removed,
        }

    # single-string path -> flags dict
    out = classify_text(text_or_segments, threshold=threshold, emit_receipt=False)
    f = out.get("flags", {})
    if categories:
        cats = set(categories)
        f = {k: v for k, v in f.items() if k in cats}
    return f
