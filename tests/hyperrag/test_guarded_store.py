import pytest
from apps.hyperrag.model import new_id, Entity, HyperEdge
from apps.hyperrag.guarded_store import GuardedGraphStore, MinimalMemoryGraphStore


def test_deny_blocks_all_operations():
    mem = MinimalMemoryGraphStore()
    gs = GuardedGraphStore(inner=mem, check=lambda a, c: "DENY")

    e = Entity(uid=new_id("ent"), etype="Concept", name="Alice")
    h = HyperEdge(
        uid=new_id("hedge"), relation="mentions", participants=[("arg", e.uid)]
    )

    with pytest.raises(PermissionError):
        gs.upsert_entity(e)
    with pytest.raises(PermissionError):
        gs.upsert_hyperedge(h)
    with pytest.raises(PermissionError):
        gs.relate(h)

    assert e.uid not in mem.entities
    assert h.uid not in mem.hyperedges
    assert h.uid not in mem.relations


def test_allow_delegates_to_inner_store():
    mem = MinimalMemoryGraphStore()
    gs = GuardedGraphStore(inner=mem, check=lambda a, c: "ALLOW")

    e = Entity(uid=new_id("ent"), etype="Concept", name="Alice")
    h = HyperEdge(
        uid=new_id("hedge"), relation="mentions", participants=[("arg", e.uid)]
    )

    gs.upsert_entity(e)
    gs.upsert_hyperedge(h)
    gs.relate(h)

    assert e.uid in mem.entities
    assert h.uid in mem.hyperedges
    assert h.uid in mem.relations
