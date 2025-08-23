from apps.provenance.prov_logging import build_ingestion_event
from apps.provenance.neo4j_write import write_ingestion_event


class _StubResult:
    def consume(self):
        class _Counters:
            nodes_created = 3
            relationships_created = 2
            properties_set = 9

        class _Summary:
            counters = _Counters()

        return _Summary()


class _StubSession:
    def __init__(self, recorder):
        self.recorder = recorder

    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc, tb):
        return False

    def run(self, cypher: str):
        self.recorder["ran"] = True
        self.recorder["cypher"] = cypher
        return _StubResult()


class _StubDriver:
    def __init__(self, recorder):
        self.recorder = recorder

    def session(self):
        return _StubSession(self.recorder)

    def close(self):
        self.recorder["closed"] = True


def test_write_ingestion_event_uses_injected_driver_and_runs_cypher():
    rec = {}
    driver = _StubDriver(rec)
    ev = build_ingestion_event("doc_X", "agent_local")
    out = write_ingestion_event(ev, driver=driver)
    assert rec.get("ran") is True
    assert "MERGE (doc:Entity:Document" in rec.get("cypher", "")
    assert out["ok"] is True
    assert out["counters"]["nodes_created"] == 3
    assert out["counters"]["relationships_created"] == 2
    assert out["counters"]["properties_set"] == 9
    assert rec.get("closed") is None
