from __future__ import annotations

from dataclasses import dataclass, field
from datetime import datetime
from typing import Dict, Iterable, List, Optional

ISO_FORMATS = ("%Y-%m-%dT%H:%M:%S%z", "%Y-%m-%dT%H:%M:%S", "%Y-%m-%d")


def _parse(ts: Optional[str]) -> Optional[datetime]:
    if ts is None or str(ts).strip() == "":
        return None
    s = str(ts).strip().replace("Z", "+00:00")
    for fmt in ISO_FORMATS:
        try:
            return datetime.strptime(s, fmt)
        except ValueError:
            continue
    # Try fromisoformat as a last resort
    try:
        return datetime.fromisoformat(s)
    except Exception:
        raise ValueError(f"Unsupported timestamp: {ts!r}")


@dataclass(frozen=True)
class TemporalSpan:
    start: Optional[datetime] = None  # inclusive
    end: Optional[datetime] = None  # exclusive

    @staticmethod
    def from_strings(start: Optional[str], end: Optional[str]) -> "TemporalSpan":
        return TemporalSpan(_parse(start), _parse(end))

    def overlaps(self, other: "TemporalSpan") -> bool:
        a0, a1, b0, b1 = self.start, self.end, other.start, other.end
        # Treat None as unbounded
        left = max(t for t in (a0, b0) if t is not None) if (a0 and b0) else (a0 or b0)
        right_candidates = [t for t in (a1, b1) if t is not None]
        right = min(right_candidates) if right_candidates else None
        return right is None or (left is None or left < right)

    def within(self, other: "TemporalSpan") -> bool:
        if other.start and (not self.start or self.start < other.start):
            return False
        if other.end and (not self.end or self.end > other.end):
            return False
        return True


@dataclass(frozen=True)
class TemporalHyperedge:
    head: str
    relation: str
    tail: str
    span: TemporalSpan = field(default_factory=TemporalSpan)
    qualifiers: Dict[str, str] = field(default_factory=dict)


def temporal_filter(
    edges: Iterable[TemporalHyperedge],
    window: TemporalSpan,
    mode: str = "overlap",
) -> List[TemporalHyperedge]:
    out: List[TemporalHyperedge] = []
    for e in edges:
        ok = e.span.overlaps(window) if mode == "overlap" else e.span.within(window)
        if ok:
            out.append(e)
    return out
