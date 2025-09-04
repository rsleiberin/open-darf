from __future__ import annotations
from dataclasses import dataclass, asdict
from typing import Any, Dict, Optional
from time import time
from datetime import datetime, timezone

from .tri_state import TriState


@dataclass
class AuditEvent:
    doc_id: str
    stage: str  # ingest | kg | extract | eval
    decision: TriState
    rule_id: Optional[str] = None
    rationale: Optional[str] = None
    duration_ms: Optional[float] = None
    evidence: Optional[Dict[str, Any]] = None
    ts: str = ""

    def __post_init__(self) -> None:
        if not self.ts:
            self.ts = datetime.now(timezone.utc).isoformat()

    def to_dict(self) -> Dict[str, Any]:
        d = asdict(self)
        d["decision"] = self.decision.value
        return d

def now_ms() -> float:
    return time() * 1000.0

class Timer:
    def __enter__(self):
        self.t0 = now_ms()
        return self
    def __exit__(self, exc_type, exc, tb):
        self.t1 = now_ms()
        self.elapsed_ms = self.t1 - self.t0
