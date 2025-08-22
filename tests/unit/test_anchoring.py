from apps.document_processor.anchoring import (
    DocForAnchoring,
    Paragraph,
    create_anchor_hierarchy,
)


def test_anchor_shapes_and_prefix():
    doc = DocForAnchoring(
        doc_type="pdf",
        content=b"hello world",
        paragraphs=[Paragraph("hello", 0, 5), Paragraph("world", 6, 11)],
    )
    res = create_anchor_hierarchy(doc)
    assert res["base_anchor"].startswith("sha256:")
    assert len(res["paragraph_anchors"]) == 2
    assert all(":para_" in s for s in res["paragraph_anchors"])
