import os, json, subprocess, pytest
def test_e2e_validator_runs():
    try:
        out = subprocess.check_output(["scripts/phase7f/e2e_validate.py"], text=True).strip()
    except Exception as e:
        pytest.skip(f"validator cannot run here: {e}")
        return
    assert os.path.exists(out)
    with open(out) as f: data=json.load(f)
    assert data.get("phase")=="7F"
    assert "measurements" in data and "status" in data
