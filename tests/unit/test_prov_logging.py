from apps.provenance.prov_logging import build_ingestion_event, cypher_for_ingestion


def test_ingestion_cypher_contains_core_labels_and_rels():
    ev = build_ingestion_event("doc_1", "agent_local")
    q = cypher_for_ingestion(ev)
    assert "Entity:Document" in q
    assert "Activity" in q and "DocumentIngestion" in q
    assert "Agent" in q and "IngestionService" in q
    for rel in ("wasGeneratedBy", "wasAssociatedWith"):
        assert rel in q
