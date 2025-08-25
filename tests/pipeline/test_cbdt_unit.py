from apps.pipeline.process.cbdt import cbdt_pass, LABELS, LocalCBDT, NullCBDT, _select_provider  # type: ignore


def _doc(texts):
    return {
        "doc_id": "test-doc-001",
        "blocks": [{"id": f"b{i+1}", "text": t} for i, t in enumerate(texts)],
        "lang": "en",
        "mime": "text/plain",
    }


def test_label_set_stability():
    expected = (
        "loaded_language",
        "appeal_to_authority",
        "ad_hominem",
        "hyperbole",
        "hedging",
        "weasel_words",
        "selection_bias",
        "framing",
    )
    assert tuple(LABELS) == expected


def test_disabled_flag_returns_noop(monkeypatch):
    monkeypatch.delenv("PIPELINE_CBDT", raising=False)
    res = cbdt_pass(
        {}, _doc(["Clearly undeniable truth.", "Some say it might be true."])
    )
    assert res.findings == []
    assert res.summary["model"]["name"] == "NullCBDT"


def test_local_provider_deterministic(monkeypatch):
    monkeypatch.setenv("PIPELINE_CBDT", "1")
    monkeypatch.setenv("PIPELINE_CBDT_PROVIDER", "local")
    doc = _doc(["Clearly undeniable truth.", "Some say it might be true."])
    r1 = cbdt_pass({}, doc)
    r2 = cbdt_pass({}, doc)
    assert r1.summary["findings_total"] == r2.summary["findings_total"]
    assert r1.summary["counts_by_label"] == r2.summary["counts_by_label"]


def test_provider_selector():
    assert isinstance(_select_provider("local"), LocalCBDT)
    assert isinstance(_select_provider("null"), NullCBDT)
    assert isinstance(_select_provider(""), NullCBDT)
