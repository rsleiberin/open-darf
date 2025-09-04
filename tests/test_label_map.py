import os
import copy
import pytest

from tools.text2nkg.transforms.label_map import apply_label_map

def test_label_map_exact_and_canonical():
    spans = [
        {"start": 0, "end": 4, "label": "HEUR"},
        {"start": 5, "end": 9, "label": "heur"},
        {"start": 10, "end": 12, "label": "  HeUr  "},
    ]
    lm = {"HEUR": "ENT"}  # only exact provided; canonicalization should handle variants
    out = apply_label_map(spans, lm, default="UNK")
    assert [s["label"] for s in out] == ["ENT", "ENT", "ENT"]

def test_label_map_default_fallback_applied():
    spans = [
        {"start": 0, "end": 1, "label": "Other"},
        {"start": 2, "end": 3, "label": None},
    ]
    lm = {"HEUR": "ENT"}
    out = apply_label_map(spans, lm, default="UNK")
    assert [s["label"] for s in out] == ["UNK", "UNK"]

def test_label_map_preserve_when_no_default():
    spans = [
        {"start": 0, "end": 1, "label": "Other"},
        {"start": 2, "end": 3, "label": "HEUR"},
    ]
    lm = {"HEUR": "ENT"}
    out = apply_label_map(spans, lm, default=None)
    assert [s["label"] for s in out] == ["Other", "ENT"]

def test_alt_label_keys_are_tolerated():
    spans = [
        {"start": 0, "end": 1, "type": "HEUR"},
        {"start": 2, "end": 3, "tag": "heur"},
        {"start": 4, "end": 5, "category": "Other"},
    ]
    lm = {"HEUR": "ENT"}
    out = apply_label_map(spans, lm, default="UNK")
    assert [s["label"] for s in out] == ["ENT", "ENT", "UNK"]

def test_env_bypass_returns_original_labels(monkeypatch):
    monkeypatch.setenv("DARF_BYPASS_MAP", "1")
    spans = [
        {"start": 0, "end": 1, "label": "HEUR"},
        {"start": 2, "end": 3, "label": "Other"},
    ]
    lm = {"HEUR": "ENT"}
    out = apply_label_map(spans, lm, default="UNK")
    assert [s["label"] for s in out] == ["HEUR", "Other"]
