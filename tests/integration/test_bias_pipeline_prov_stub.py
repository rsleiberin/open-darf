import tempfile
from pathlib import Path
from apps.document_processor import bias

SAMPLE = "We present results but offer no methodology. Clearly this is the best outcome. [1] doi:10.1/abc"


def test_classify_text_with_provenance_stub(monkeypatch):
    with tempfile.TemporaryDirectory() as rec, tempfile.TemporaryDirectory() as prov:
        monkeypatch.setenv("RECEIPTS_PATH", rec)
        monkeypatch.setenv("CBDT_PROVENANCE", "1")
        monkeypatch.setenv("CBDT_PROV_MODE", "stub")
        monkeypatch.setenv("PROV_PATH", prov)

        out = bias.classify_text(
            SAMPLE,
            threshold=0.4,
            emit_receipt=True,
            doc_id="doc-xyz",
            segment_anchor={"start": 0, "end": 5},
        )
        assert set(out.keys()) >= {"scores", "flags", "backend", "receipt_path"}
        assert out["receipt_path"] and Path(out["receipt_path"]).exists()
        prov_files = list(Path(prov).glob("bias-prov-*.jsonl"))
        assert prov_files and prov_files[0].stat().st_size > 0
