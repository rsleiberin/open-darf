from __future__ import annotations
from dataclasses import dataclass
from typing import Dict, List, Optional, Set, Tuple
import json, os

def _norm(s: str) -> str:
    return " ".join(s.strip().split()).lower()

def _sig(principles: List[str]) -> str:
    return "|".join(sorted(_norm(p) for p in principles))

@dataclass(frozen=True)
class GovernanceConfig:
    deprecate: Set[str]
    principle_overrides: Dict[str, str]  # signature -> decision

def _load_json_from_env_or_file() -> Dict:
    raw = os.getenv("REASONING_GOVERNANCE_JSON", "").strip()
    if raw:
        try:
            return json.loads(raw)
        except Exception:
            return {}
    path = os.getenv("REASONING_GOVERNANCE_FILE", "").strip()
    if path and os.path.exists(path):
        try:
            with open(path, "r", encoding="utf-8") as f:
                return json.load(f)
        except Exception:
            return {}
    return {}

def load() -> GovernanceConfig:
    data = _load_json_from_env_or_file() or {}
    deprecate = set(map(_norm, data.get("deprecate", [])))
    pov = data.get("principle_overrides", {})
    principle_overrides = { _norm(k): v.strip().upper() for k, v in pov.items() }
    return GovernanceConfig(deprecate=deprecate, principle_overrides=principle_overrides)

def is_deprecated(cfg: GovernanceConfig, precedent_id: str) -> bool:
    return _norm(precedent_id) in cfg.deprecate

def filter_precedents(cfg: GovernanceConfig, ids: List[str]) -> List[str]:
    return [pid for pid in ids if not is_deprecated(cfg, pid)]

def maybe_override_decision(cfg: GovernanceConfig, decision: str, principles: List[str]) -> Tuple[str, bool]:
    """Return (decision_to_use, applied_flag)."""
    key = _sig(principles)
    if key in cfg.principle_overrides:
        return (cfg.principle_overrides[key], True)
    return (decision, False)
