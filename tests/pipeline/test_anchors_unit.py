from apps.pipeline.anchors import hash_text, anchors_pass


def test_hash_text_sha256_known_vector():
    # sha256("hello world")
    assert (
        hash_text("hello world")
        == "b94d27b9934d3e08a52e52d7da7dabfac484efe37a5380ee9088f7ace2efcde9"
    )


def test_sentence_subanchors_on_flag(monkeypatch):
    monkeypatch.setenv("PIPELINE_ANCHORS", "1")
    monkeypatch.setenv("PIPELINE_ANCHORS_SUB", "1")
    doc = {"doc_id": "a1", "blocks": [{"id": "b1", "text": "One. Two! Three?"}]}
    res = anchors_pass({}, doc)
    assert res.doc_anchor and len(res.sub_anchors) == 3
