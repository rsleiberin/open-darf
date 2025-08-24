import json
from pathlib import Path
import tempfile

from apps.document_processor import bias

SAMPLE = "We present results but offer no methodology. Clearly this is the best outcome. [1] doi:10.1/abc"


def test_classify_text_writes_receipt_and_returns_shape(monkeypatch):
    with tempfile.TemporaryDirectory() as d:
        monkeypatch.setenv("RECEIPTS_PATH", d)
        out = bias.classify_text(SAMPLE, threshold=0.4, emit_receipt=True)

        # shape checks
        assert set(out.keys()) >= {"scores", "flags", "backend", "receipt_path"}
        assert 0.0 <= out["scores"]["methodology_bias"] <= 1.0
        assert isinstance(out["flags"]["methodology_bias"], (float, int))

        # receipt file path provided and valid
        rp = out.get("receipt_path")
        assert isinstance(rp, str) and rp, "receipt_path missing"
        p = Path(rp)
        assert p.exists(), f"receipt file not found at {rp}"

        # last line should be valid JSON with component marker
        last = p.read_text().strip().splitlines()[-1]
        data = json.loads(last)
        assert data.get("component") == "cbdt_bias"
        assert "scores" in data and "flags" in data
