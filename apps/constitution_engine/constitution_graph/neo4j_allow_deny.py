"""
Constitutional graph helpers to expose ALLOW/DENY existence flags.

This module provides:
- build_allow_deny_cypher(): a parameterized Cypher query template
- parse_allow_deny(records): robust reduction of Neo4j result records -> (allow_exists, deny_exists)

Design notes:
- We don't require a live Neo4j driver in import path; runtime querying can be layered in elsewhere.
- Parsing is defensive: any record with a truthy allow_exists sets allow=True; same for deny_exists.
- Missing keys default to False.
"""

from typing import Iterable, Mapping, Tuple


def build_allow_deny_cypher() -> str:
    """
    Returns a conservative Cypher template that implementers can refine.
    It checks for *existence* of any matching ALLOW/DENY policy path—schema-agnostic by design.

    Parameters expected:
      $principal_id, $action_id, $resource_id
    """
    return (
        "MATCH (p:Principal {id: $principal_id}) "
        "MATCH (a:Action {id: $action_id}) "
        "MATCH (r:Resource {id: $resource_id}) "
        "OPTIONAL MATCH pathAllow = (p)-[*1..4]->(:Policy {effect: 'ALLOW'})-[:APPLIES_TO]->(a) "
        "OPTIONAL MATCH pathDeny  = (p)-[*1..4]->(:Policy {effect: 'DENY'})-[:APPLIES_TO]->(a) "
        "RETURN "
        "  coalesce(pathAllow IS NOT NULL, false) AS allow_exists, "
        "  coalesce(pathDeny  IS NOT NULL, false) AS deny_exists"
    )


def parse_allow_deny(records: Iterable[Mapping[str, object]]) -> Tuple[bool, bool]:
    """
    Reduce Neo4j records into (allow_exists, deny_exists) booleans.

    Any record with truthy 'allow_exists' flips allow to True; same for 'deny_exists'.
    Missing keys are treated as False. Empty iterables return (False, False).
    """
    allow = False
    deny = False
    for rec in records or ():
        # accept both dict-like and object-like with attributes
        a = None
        d = None
        if isinstance(rec, Mapping):
            a = rec.get("allow_exists", False)
            d = rec.get("deny_exists", False)
        else:
            a = getattr(rec, "allow_exists", False)
            d = getattr(rec, "deny_exists", False)
        if a:
            allow = True
        if d:
            deny = True
        # short-circuit if both True
        if allow and deny:
            break
    return allow, deny
