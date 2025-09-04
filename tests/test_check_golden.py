import json, subprocess, sys
from pathlib import Path

def _write_scoreboard(path: Path, f1: float):
    path.write_text(json.dumps({"strict": {"f1": f1}}, indent=2), encoding="utf-8")

def test_check_golden_pass(tmp_path: Path):
    dev = tmp_path/"dev.json"; _write_scoreboard(dev, 0.2049)
    test = tmp_path/"test.json"; _write_scoreboard(test, 0.2045)
    # Use defaults ~0.20485/0.20446, tol 0.002 -> should pass
    proc = subprocess.run(
        [sys.executable, "tools/text2nkg/check_golden.py", "--dev-scoreboard", str(dev), "--test-scoreboard", str(test), "--tol", "0.002"],
        capture_output=True, text=True
    )
    assert proc.returncode == 0, proc.stdout + proc.stderr

def test_check_golden_fail(tmp_path: Path):
    dev = tmp_path/"dev.json"; _write_scoreboard(dev, 0.30)   # too high
    test = tmp_path/"test.json"; _write_scoreboard(test, 0.10) # too low
    proc = subprocess.run(
        [sys.executable, "tools/text2nkg/check_golden.py", "--dev-scoreboard", str(dev), "--test-scoreboard", str(test), "--tol", "0.002"],
        capture_output=True, text=True
    )
    assert proc.returncode == 3, proc.stdout + proc.stderr
