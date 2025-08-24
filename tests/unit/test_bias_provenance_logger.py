from apps.provenance.doc_biaso import load_doc_biaso_ontology
from apps.provenance.bias_logger import (
    get_bias_logger,
    get_stub_events,
    make_bias_annotation,
)


def test_doc_biaso_mapping_basic():
    dbo = load_doc_biaso_ontology()
    assert dbo.classify_bias_type("methodology_bias").endswith("MethodologyBias")
    assert dbo.classify_bias_type("unknown") == "doc-biaso:UnknownBias"


def test_stub_logger_records_event(monkeypatch):
    monkeypatch.setenv("CBDT_PROVENANCE", "1")
    monkeypatch.setenv("CBDT_PROV_MODE", "stub")
    logger = get_bias_logger()
    ann = make_bias_annotation(
        segment_anchor={"start": 0, "end": 10},
        scores={"citation_bias": 0.2, "methodology_bias": 0.7},
        flags={"citation_bias": 0.0, "methodology_bias": 1.0},
        backend="tiny-0.1",
        threshold=0.5,
    )
    logger.log_annotation(document_id="doc-1", annotation=ann)
    events = get_stub_events()
    assert events and events[-1]["annotation"]["ontology_classification"].startswith(
        "doc-biaso:"
    )
