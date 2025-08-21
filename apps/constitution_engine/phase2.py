# --- Phase-2 scaffold: tri-state + fail-closed env gate ---
from __future__ import annotations
from dataclasses import dataclass, field
from enum import Enum
import os
from typing import Dict

class Decision(Enum):
    ALLOW = "ALLOW"
    DENY = "DENY"
    INDETERMINATE = "INDETERMINATE"

@dataclass
class ValidationResult:
    decision: Decision
    reason_code: str = ""
    metrics: Dict[str, int] = field(default_factory=lambda: {
        "neo4j_roundtrips": 0,
        "cache_hits": 0,
        "cache_misses": 0,
    })

def _fail_closed_default() -> ValidationResult:
    """
    Use fail-closed by default when schema is absent or DB is unreachable.
    Allow a local/dev override via ENGINE_FAIL_OPEN=true.
    """
    if os.getenv("ENGINE_FAIL_OPEN", "false").lower() in ("1", "true", "yes"):
        return ValidationResult(Decision.ALLOW, "fail_open:dev_override")
    return ValidationResult(Decision.INDETERMINATE, "neo4j_schema_missing:fail_closed")
