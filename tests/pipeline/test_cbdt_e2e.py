import json
from pathlib import Path
from apps.pipeline.process.cbdt import cbdt_pass  # type: ignore


def _doc(doc_id="micro-001"):
    return {
        "doc_id": doc_id,
        "blocks": [
            {"id": "b1", "text": "This is clearly undeniable."},
            {"id": "b2", "text": "Some say it might be true."},
            {"id": "b3", "text": "Experts say this is correct."},
        ],
        "lang": "en",
        "mime": "text/plain",
    }


def test_receipt_written_when_perf_and_flag_on(monkeypatch):
    monkeypatch.setenv("PIPELINE_CBDT", "1")
    monkeypatch.setenv("PIPELINE_CBDT_PROVIDER", "local")
    monkeypatch.setenv("PIPELINE_PERF", "1")

    res = cbdt_pass({}, _doc("e2e-micro-001"))
    assert res.summary["findings_total"] >= 1

    base = Path("docs/audit/pipeline/pipeline_cbdt")
    assert base.exists()

    # Prefer explicit paths from summary
    candidates = []
    for k in ("receipt_path", "receipt_last"):
        p = res.summary.get(k)
        if p and Path(p).exists():
            candidates.append(Path(p))

    # Fallback: scan all receipts and match doc_id by content
    if not candidates:
        for p in sorted(base.rglob("*.json")):
            try:
                payload = json.loads(p.read_text(encoding="utf-8"))
                if payload.get("doc_id") == "e2e-micro-001":
                    candidates.append(p)
                    break
            except Exception:
                pass

    assert candidates, f"no receipts found for e2e-micro-001 under {base}"
    # Basic shape checks
    payload = json.loads(candidates[-1].read_text(encoding="utf-8"))
    for k in ("pipeline_run_id", "doc_id", "timing_ms", "counters", "model", "flags"):
        assert k in payload
