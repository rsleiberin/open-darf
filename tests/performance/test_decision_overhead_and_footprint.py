import os
import glob
import pytest


def _latest(patterns):
    if isinstance(patterns, (list, tuple)):
        pats = [str(p) for p in patterns]
    else:
        pats = [str(patterns)]
    paths = []
    for p in pats:
        paths.extend(glob.glob(p))
    if not paths:
        pytest.skip(f"no receipts found for patterns={pats}")
    return max(paths, key=os.path.getmtime)


def test_decision_overhead_receipt_present():
    p = _latest("var/receipts/phase6/validation/decision_overhead/*/overhead.json")
    assert os.path.exists(p), f"missing: {p}"


def test_audit_footprint_present():
    p = _latest("var/receipts/phase6/validation/decision_overhead/*/footprint.json")
    assert os.path.exists(p), f"missing: {p}"
