from __future__ import annotations
from typing import List, Dict, Any, Iterable, Tuple

def ensure_indexes(driver) -> None:
    """Create basic indexes/constraints for Precedent nodes (id unique)."""
    cy = [
        "CREATE CONSTRAINT precedent_id IF NOT EXISTS FOR (p:Precedent) REQUIRE p.id IS UNIQUE",
        "CREATE INDEX precedent_principles IF NOT EXISTS FOR (p:Precedent) ON (p.principles)"
    ]
    with driver.session() as s:
        for q in cy:
            s.run(q)

def get_all_principles(driver) -> List[Dict[str, Any]]:
    """Return list of {id, principles, decision?, rationale?}."""
    q = "MATCH (p:Precedent) RETURN p.id AS id, p.principles AS principles, p.decision AS decision, p.rationale AS rationale"
    out: List[Dict[str, Any]] = []
    with driver.session() as s:
        for rec in s.run(q):
            out.append(dict(rec))
    return out

def cooccurrence(driver, min_count: int = 2) -> List[Tuple[str, int]]:
    """Return principle co-occurrence counts across precedents."""
    # Pull to Python and count quickly (avoids complex APOC dependency)
    items = get_all_principles(driver)
    from collections import Counter
    c = Counter()
    for it in items:
        ps = set(it.get("principles") or [])
        for p in ps:
            c[p] += 1
    return [(k, v) for k, v in c.items() if v >= min_count]
