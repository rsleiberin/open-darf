from __future__ import annotations
from typing import Dict, Iterable, List, Tuple, DefaultDict
from collections import defaultdict

# A simple "fact" triple: (head, role, tail)
Fact = Tuple[str, str, str]


class IndexSim:
    """
    Lightweight, service-free indexes for local sanity/perf testing.
    - adjacency[role][head] -> list[str] of tails
    - fanout[role][head] -> int (#neighbors under role)
    """

    def __init__(self, facts: Iterable[Fact]) -> None:
        adj: DefaultDict[str, DefaultDict[str, List[str]]] = defaultdict(
            lambda: defaultdict(list)
        )
        for h, r, t in facts:
            adj[r][h].append(t)
        self.adjacency: Dict[str, Dict[str, List[str]]] = {
            r: dict(hmap) for r, hmap in adj.items()
        }
        # fanouts
        self.fanout: Dict[str, Dict[str, int]] = {
            r: {h: len(tails) for h, tails in hmap.items()}
            for r, hmap in self.adjacency.items()
        }

    def neighbors(self, head: str, role: str | None = None) -> List[str]:
        """
        Return neighbors of 'head'. If role is None, union over all roles.
        """
        if role is not None:
            return list(self.adjacency.get(role, {}).get(head, []))
        # union across roles (dedup preserve insertion)
        seen = set()
        out: List[str] = []
        for rmap in self.adjacency.values():
            for t in rmap.get(head, []):
                if t not in seen:
                    seen.add(t)
                    out.append(t)
        return out

    def fanout_count(self, head: str, role: str | None = None) -> int:
        if role is not None:
            return int(self.fanout.get(role, {}).get(head, 0))
        # sum across roles
        return sum(self.fanout.get(r, {}).get(head, 0) for r in self.fanout)
