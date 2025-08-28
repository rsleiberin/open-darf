import os
import glob
import json
import pytest

RUN_PERF = os.environ.get("RUN_PERF", "0") == "1"
pytestmark = pytest.mark.skipif(
    not RUN_PERF, reason="RUN_PERF=1 required for perf tests"
)


def _latest(patterns):
    paths = []
    for pat in patterns:
        paths.extend(glob.glob(pat))
    return max(paths, key=os.path.getmtime) if paths else None


def test_biored_perf_receipt_present_and_reasonable():
    p = _latest(["var/receipts/phase6/validation/biored/*/perf/aggregate_perf.json"])
    assert p and os.path.exists(p), "BioRED perf aggregate missing"
    j = json.load(open(p, "r", encoding="utf-8"))
    # Expect keys and mean >= 0
    any_split = any("per_doc" in v for v in j.values())
    assert any_split, "No per_doc section in BioRED perf aggregate"


def test_scierc_eval_summary_present():
    p = _latest(["var/receipts/phase6/validation/scierc/*/eval/summary.json"])
    assert p and os.path.exists(p), "SciERC eval summary missing"
    j = json.load(open(p, "r", encoding="utf-8"))
    assert "latency_seconds" in j, "SciERC summary missing latency_seconds"
