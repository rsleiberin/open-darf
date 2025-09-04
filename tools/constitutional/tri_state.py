from __future__ import annotations
from enum import Enum


class TriState(str, Enum):
    ACCEPTABLE = "ACCEPTABLE"
    REJECTED = "REJECTED"
    PENDING = "PENDING"

    @classmethod
    def from_str(cls, s: str) -> "TriState":
        s_norm = (s or "").strip().upper()
        try:
            return cls[s_norm]
        except KeyError:
            # Also accept value forms
            for v in cls:
                if v.value == s_norm:
                    return v
            raise ValueError(f"Unknown TriState: {s}")
