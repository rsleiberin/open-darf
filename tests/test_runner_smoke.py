import json, subprocess, sys, os
from pathlib import Path

def test_runner_smoke_cli(tmp_path: Path):
    outdir = tmp_path / "run"
    cmd = [
        sys.executable, "tools/text2nkg/run_eval_scored.py",
        "--dataset","biored","--split","dev","--outdir",str(outdir),
        "--smoke","--write-docs-scoreboard"
    ]
    env = dict(os.environ)
    env["DARF_BYPASS_MAP"] = ""  # ensure mapping active
    proc = subprocess.run(cmd, env=env, capture_output=True, text=True)
    assert proc.returncode == 0, proc.stderr
    # Verify receipts
    m = json.loads(Path(outdir/"metrics.json").read_text())
    s = json.loads(Path(outdir/"scoreboard.json").read_text())
    assert "strict" in s and "unlabeled_boundary" in s
    assert isinstance(m.get("skipped_invalid_pred_spans"), int)
    assert isinstance(m.get("label_histogram"), dict)
    assert m.get("run_meta", {}).get("pred_count") is not None
    assert "adapter" in m and m["adapter"] in ("smoke_adapter","from_paths")
    # Docs scoreboard exists
    assert list(Path("docs/scoreboards").glob("biored_dev_scoreboard_*.json"))
