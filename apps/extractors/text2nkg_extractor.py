from __future__ import annotations
import os
import re
from typing import Any, Dict, List
from apps.guards import constitutional as constitutional_guard
from apps.knowledge_graph.hypergraph import HyperEdge, Role, asdict_edge

_SIMPLE_VERB_RE = re.compile(
    r"^\s*(?P<subj>[\w\-\s]+?)\s+(?P<verb>\b(contains|causes|prevents|enables|uses|produces|belongs|participates)\b)\s+(?P<obj>[\w\-\s]+?)\.?\s*$",
    re.I,
)


class Text2NKGExtractor:
    """
    Text2NKG: convert text into n-ary hyperedges with role slots.
    - Gate: EXTRACTOR_TEXT2NKG=1
    - This scaffold uses a simple pattern; production can swap in a ML model behind same interface.
    """

    def __init__(self) -> None:
        self.enabled = os.getenv("EXTRACTOR_TEXT2NKG", "0") == "1"

    def is_enabled(self) -> bool:
        return self.enabled

    def extract(self, text: str) -> Dict[str, Any]:
        pre = constitutional_guard.evaluate({"text": text})
        if pre.decision == "DENY":
            return {
                "decision": "DENY",
                "reason_code": pre.reason_code,
                "relations": [],
                "provenance": {"stage": "pre_guard"},
            }

        if not self.enabled:
            return {
                "decision": pre.decision,
                "reason_code": "disabled",
                "relations": [],
                "provenance": {"enabled": False, "stage": "disabled_stub"},
            }

        m = _SIMPLE_VERB_RE.match(text or "")
        edges: List[HyperEdge] = []
        if m:
            subj, verb, obj = (
                m.group("subj").strip(),
                m.group("verb").lower(),
                m.group("obj").strip(),
            )
            # Guard each role text; DENY precedence across roles
            dec = pre.decision
            rs = []
            for name, val in (("subject", subj), ("predicate", verb), ("object", obj)):
                g = constitutional_guard.evaluate({"text": val})
                dec = constitutional_guard.precedence(dec, g.decision)
                rs.append(
                    Role(
                        name=name,
                        text=val,
                        label="ENTITY",
                        meta={"guard": g.decision, "reason": g.reason_code},
                    )
                )
            e = HyperEdge(
                relation=verb,
                roles=rs,
                score=0.75,
                guard_decision=dec,
                reason_code="ok",
                provenance={"model": "regex_stub"},
            )
            edges.append(e)
        else:
            # No relation found; safe INDETERMINATE
            return {
                "decision": "INDETERMINATE",
                "reason_code": "no_relation",
                "relations": [],
                "provenance": {"enabled": True, "stage": "parse"},
            }

        # Finalize decision across edges (if more than one later)
        final = pre.decision
        for e in edges:
            final = constitutional_guard.precedence(final, e.guard_decision)
        return {
            "decision": final,
            "reason_code": "ok",
            "relations": [asdict_edge(e) for e in edges],
            "provenance": {
                "enabled": True,
                "stage": "inference",
                "impl": "Text2NKGExtractor",
            },
        }
