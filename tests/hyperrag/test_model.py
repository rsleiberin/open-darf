from apps.hyperrag.model import Entity, Span, HyperEdge, Fact, new_id


def test_entity_roundtrip_minimal():
    e = Entity(
        uid=new_id("ent"), etype="Concept", name="Alice", span=Span(0, 5, "Alice")
    )
    assert e.uid.startswith("ent_")
    assert e.name == "Alice"


def test_hyperedge_fact_json():
    e1 = Entity(uid=new_id("ent"), etype="Concept", name="Alice")
    e2 = Entity(uid=new_id("ent"), etype="Concept", name="ACME")
    h = HyperEdge(
        uid=new_id("hedge"),
        relation="works_at",
        participants=[("subject", e1.uid), ("object", e2.uid)],
    )
    f = Fact(uid=new_id("fact"), edge=h, confidence=0.42)
    js = f.to_json()
    assert '"relation":"works_at"' in js
    assert '"confidence":0.42' in js
