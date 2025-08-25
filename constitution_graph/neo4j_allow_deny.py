"""
Constitutional graph helpers to expose ALLOW/DENY existence flags.

Exports:
- build_allow_deny_cypher(): parameterized Cypher that yields allow_exists/deny_exists booleans
- parse_allow_deny(records): reduce query records -> (allow_exists, deny_exists)

Notes:
- Schema-agnostic template: uses effect 'ALLOW'/'DENY' on :Policy and bounded traversal fanout.
- Import-safe: no driver imports at module import time.
"""

from typing import Iterable, Mapping, Tuple


def build_allow_deny_cypher() -> str:
    """
    Returns a conservative Cypher template that checks existence of ALLOW/DENY paths.

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
    if not records:
        return (False, False)
    for rec in records:
        if isinstance(rec, Mapping):
            a = rec.get("allow_exists", False)
            d = rec.get("deny_exists", False)
        else:
            a = getattr(rec, "allow_exists", False)
            d = getattr(rec, "deny_exists", False)
        allow = bool(allow or a)
        deny = bool(deny or d)
        if allow and deny:
            break
    return (allow, deny)
