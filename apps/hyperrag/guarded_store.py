from __future__ import annotations
from typing import Callable, Dict, List, Optional
from .model import Entity, HyperEdge
from .store import GraphStore
from .guard import evaluate_action


class MinimalMemoryGraphStore:
    def __init__(self) -> None:
        self.entities: Dict[str, Entity] = {}
        self.hyperedges: Dict[str, HyperEdge] = {}
        self.relations: List[str] = []

    def upsert_entity(self, e: Entity) -> None:
        self.entities[e.uid] = e

    def upsert_hyperedge(self, h: HyperEdge) -> None:
        self.hyperedges[h.uid] = h

    def relate(self, h: HyperEdge) -> None:
        self.relations.append(h.uid)


CheckFn = Callable[[str, Dict], str]


class GuardedGraphStore:
    def __init__(
        self, inner: Optional[GraphStore] = None, check: Optional[CheckFn] = None
    ) -> None:
        self.inner = inner or MinimalMemoryGraphStore()
        self.check: CheckFn = check or (lambda action, ctx: evaluate_action(action, ctx))  # type: ignore[return-value]

    def _enforce(self, action: str, ctx: Dict) -> None:
        decision = (self.check(action, ctx) or "DENY").upper()
        if decision != "ALLOW":
            raise PermissionError(f"constitutional_guard:{decision}:{action}")

    def upsert_entity(self, e: Entity) -> None:
        self._enforce("graph.upsert_entity", {"etype": e.etype})
        self.inner.upsert_entity(e)

    def upsert_hyperedge(self, h: HyperEdge) -> None:
        self._enforce(
            "graph.upsert_hyperedge",
            {"relation": h.relation, "arity": len(h.participants)},
        )
        self.inner.upsert_hyperedge(h)

    def relate(self, h: HyperEdge) -> None:
        self._enforce("graph.relate", {"relation": h.relation})
        self.inner.relate(h)
