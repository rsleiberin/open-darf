from __future__ import annotations
from dataclasses import dataclass, field
from typing import Dict, Any, List


@dataclass
class Role:
    name: str
    text: str
    label: str = "ENTITY"
    meta: Dict[str, Any] = field(default_factory=dict)


@dataclass
class HyperEdge:
    relation: str
    roles: List[Role]
    score: float = 0.0
    guard_decision: str = "INDETERMINATE"
    reason_code: str = "unset"
    provenance: Dict[str, Any] = field(default_factory=dict)


def asdict_edge(e: HyperEdge) -> Dict[str, Any]:
    return {
        "relation": e.relation,
        "roles": [
            {"name": r.name, "text": r.text, "label": r.label, "meta": r.meta}
            for r in e.roles
        ],
        "score": e.score,
        "guard_decision": e.guard_decision,
        "reason_code": e.reason_code,
        "provenance": e.provenance,
    }
