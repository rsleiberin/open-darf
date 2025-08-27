from apps.knowledge_graph.temporal_model import TemporalModel, parse_timespan
from apps.knowledge_graph.entity_extraction import extract_all


def test_temporal_disabled_stub(monkeypatch):
    monkeypatch.setenv("TEMPORAL_GRAPH_MODEL", "0")
    out = TemporalModel().infer("Project ran from 2019 to 2021")
    assert out["reason_code"] == "disabled"
    assert out["events"] == []


def test_parse_timespan_years():
    ts = parse_timespan("operated from 2018 to 2020")
    assert ts and ts.start.startswith("2018") and ts.end.startswith("2020")


def test_orchestrator_temporal_path(monkeypatch):
    monkeypatch.setenv("EXTRACTOR_SCI", "0")
    monkeypatch.setenv("EXTRACTOR_BIO", "0")
    monkeypatch.setenv("EXTRACTOR_TEXT2NKG", "0")
    monkeypatch.setenv("TEMPORAL_GRAPH_MODEL", "1")
    out = extract_all("System migrated from 2017 to 2019")
    assert (
        "temporals" in out and out["temporals"]
    ), "temporals should surface when temporal model enabled"
