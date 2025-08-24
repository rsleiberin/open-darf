import tempfile
from apps.document_processor import bias

SAMPLE = "Clearly, the men were the best performers in the study. [1] doi:10.1/abc"


def test_pipeline_with_oscar_neutralization(monkeypatch):
    with tempfile.TemporaryDirectory() as rec:
        monkeypatch.setenv("RECEIPTS_PATH", rec)
        out = bias.classify_text(
            SAMPLE, neutralize=True, min_fidelity=0.95, emit_receipt=True
        )
        assert "neutralizations" in out
        nz = out["neutralizations"]
        assert isinstance(nz, dict)
        assert "text" in nz and "changes" in nz and "human_review" in nz
        assert (nz["changes"] and all("fidelity" in c for c in nz["changes"])) or nz[
            "human_review"
        ] is True
