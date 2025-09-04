import pytest
from tools.text2nkg.emit_nkg import assert_valid_spans

def test_accepts_core_shape_and_aliases():
    spans = [
        {"start": 0, "end": 4, "label": "A"},
        {"begin": 5, "end": 9, "type": "B"},
        {"start": "10", "stop": "14", "tag": "C"},  # numeric strings
        {"offset_start": 15, "offset_end": 20, "category": "D"},
    ]
    ok, bad = assert_valid_spans(spans)
    assert [s["label"] for s in ok] == ["A", "B", "C", "D"]
    assert [ (s["start"], s["end"]) for s in ok ] == [(0,4),(5,9),(10,14),(15,20)]
    assert bad == 0

def test_rejects_invalid_and_preserves_order_of_valid():
    spans = [
        {"start": 0, "end": 1, "label": "ok1"},
        {"start": 5, "end": 5, "label": "bad_equal"},   # end == start
        {"start": -1, "end": 2, "label": "bad_negative"},
        "not_a_mapping",
        {"start": 3, "end": 6, "label": "ok2"},
    ]
    ok, bad = assert_valid_spans(spans)
    assert [s["label"] for s in ok] == ["ok1", "ok2"]
    assert bad == 3

def test_non_string_labels_are_coerced_to_str():
    spans = [
        {"start": 0, "end": 2, "label": 123},
        {"start": 3, "end": 5, "label": None},
    ]
    ok, bad = assert_valid_spans(spans)
    assert ok[0]["label"] == "123"
    assert ok[1]["label"] is None
    assert bad == 0

def test_empty_and_none_inputs():
    ok, bad = assert_valid_spans([])
    assert ok == [] and bad == 0
    ok, bad = assert_valid_spans(None)
    assert ok == [] and bad == 0
