from __future__ import annotations
from dataclasses import dataclass
from typing import Dict, Any, List, Optional, Tuple
import hashlib
import os
import re
import time


@dataclass
class Anchor:
    """A single anchor for a span of text."""

    id: str  # hex digest
    start: int  # byte offset start (utf-8)
    end: int  # byte offset end (utf-8)
    text: Optional[str] = None  # may be omitted in prod


@dataclass
class AnchorResult:
    doc_id: str
    algo: str
    doc_anchor: str
    sub_anchors: List[Anchor]
    timing_ms: float


def _on(key: str) -> bool:
    return str(os.getenv(key, "")).strip().lower() in {"1", "true", "yes", "on"}


def hash_text(text: str, algo: str = "sha256") -> str:
    h = hashlib.new(algo)
    # Use .encode to be explicit (utf-8); ignore errors for determinism
    h.update((text or "").encode("utf-8", errors="ignore"))
    return h.hexdigest()


_SENT_SPLIT = re.compile(r"(?<=[.!?])\s+")


def _sentence_spans(text: str) -> List[Tuple[int, int]]:
    if not text:
        return []
    # naive split to keep fast/CI-safe; compute byte offsets for spans
    parts = _SENT_SPLIT.split(text)
    spans: List[Tuple[int, int]] = []
    cursor = 0
    for i, part in enumerate(parts):
        if not part:
            continue
        start = cursor
        end = start + len(part)
        spans.append((start, end))
        # advance cursor by part + one separator if exists
        if i < len(parts) - 1:
            # find the separator length by searching in original text
            sep_idx = start + len(part)
            # consume consecutive whitespace after the sentence
            while sep_idx < len(text) and text[sep_idx].isspace():
                sep_idx += 1
            cursor = sep_idx
        else:
            cursor = end
    return spans


def anchors_pass(ctx: Optional[Dict[str, Any]], doc: Dict[str, Any]) -> AnchorResult:
    """
    Compute document-level SHA-256 anchor and sub-anchors (sentence-level).
    Flag-gated via PIPELINE_ANCHORS=1; default off to keep PR CI fast.
    """
    t0 = time.perf_counter()
    algo = os.getenv("PIPELINE_ANCHOR_ALGO", "sha256")
    doc_id = str(doc.get("doc_id", "unknown"))
    blocks = doc.get("blocks", [])
    text = ""
    if blocks and isinstance(blocks[0], dict):
        # Use first block text for now (runner feeds full text as single block)
        text = blocks[0].get("text") or ""
    elif isinstance(blocks, list) and blocks and hasattr(blocks[0], "text"):
        text = getattr(blocks[0], "text") or ""
    else:
        text = doc.get("text", "") or ""

    doc_hex = hash_text(text, algo)

    subs: List[Anchor] = []
    if _on("PIPELINE_ANCHORS_SUB"):  # optional sub-anchors
        for start, end in _sentence_spans(text):
            seg = text[start:end]
            subs.append(
                Anchor(
                    id=hash_text(seg, algo),
                    start=len(text[:start].encode("utf-8", errors="ignore")),
                    end=len(text[:end].encode("utf-8", errors="ignore")),
                    text=None,  # omit raw segment by default to avoid PII
                )
            )

    timing_ms = (time.perf_counter() - t0) * 1000.0
    return AnchorResult(
        doc_id=doc_id,
        algo=algo,
        doc_anchor=doc_hex,
        sub_anchors=subs,
        timing_ms=timing_ms,
    )
