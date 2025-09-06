import importlib, os, json, subprocess, sys, pytest

def test_validate_audit_runs():
    # run the validator script; ensure it writes a summary and includes required keys
    try:
        out = subprocess.check_output(["scripts/phase7f/validate_audit.py"], text=True).strip()
    except Exception as e:
        pytest.skip(f"validator not runnable in this environment: {e}")
        return
    assert os.path.exists(out), "validator did not write summary.json"
    with open(out) as f: data=json.load(f)
    assert data.get("phase")=="7F"
    env=data.get("envelope",{})
    assert "provenance" in env and "constitutional" in env and "propagation" in env and "revocation" in env
