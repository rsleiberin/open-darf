from __future__ import annotations
from dataclasses import dataclass
from typing import Dict, List, Tuple


@dataclass(frozen=True)
class Span:
    id: str
    start: int
    end: int
    level: str = "line"
    page: int | None = None
    rect: Tuple[float, float, float, float] | None = None  # PDF coords optional


def chunk_linebreaks(doc_bytes: bytes) -> List[Span]:
    """Split by newline; produce byte spans that map back into the original bytes exactly."""
    spans: List[Span] = []
    start = 0
    idx = 0
    b = doc_bytes
    for i, ch in enumerate(b):
        if ch == 0x0A:  # '\n'
            if i > start:
                spans.append(Span(id=f"s{idx}", start=start, end=i, level="line"))
                idx += 1
            start = i + 1
    if start < len(b):
        spans.append(Span(id=f"s{idx}", start=start, end=len(b), level="line"))
    return spans


def make_manifest_v1(
    doc_digest: str, doc_bytes: bytes, mime: str, spans: List[Span], provenance: Dict
) -> Dict:
    return {
        "schema": "smg/span-manifest@v1",
        "doc": {"digest": doc_digest, "mime": mime, "bytes": len(doc_bytes)},
        "provenance": provenance,
        "chunking": {"method": "linebreak", "params": {}},
        "spans": [
            {
                "id": s.id,
                "uri": f"cas:sha256:{doc_digest}#byte={s.start}-{s.end}",
                "level": s.level,
                "page": s.page,
                "rect": s.rect,
            }
            for s in spans
        ],
    }
