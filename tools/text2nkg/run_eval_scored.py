from __future__ import annotations
import argparse, json, os, sys, time, shutil
from pathlib import Path
from typing import Dict, List, Mapping, Optional, Tuple

from tools.text2nkg.transforms.label_map import apply_label_map
from tools.text2nkg.emit_nkg import assert_valid_spans
from tools.text2nkg.pipeline import compute_metrics

def _now_stamp() -> str:
    return time.strftime("%Y%m%d-%H%M%S", time.gmtime())

def _read_json(path: Path) -> Dict:
    with open(path, "r", encoding="utf-8") as f:
        return json.load(f)

def _write_json(path: Path, obj) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with open(path, "w", encoding="utf-8") as f:
        json.dump(obj, f, ensure_ascii=False, indent=2, sort_keys=True)

def _smoke_data() -> Tuple[List[dict], List[dict]]:
    # Minimal 2-span sample; one alias-bound case to exercise validator
    preds = [
        {"start": 0, "end": 4, "label": "HEUR"},
        {"begin": 6, "end": 10, "type": "heur"},
        {"start": 10, "end": 10, "label": "X"},  # invalid
    ]
    gold = [
        {"start": 0, "end": 4, "label": "ENT"},
        {"start": 6, "end": 10, "label": "ENT"},
    ]
    return preds, gold

def _load_config(path: Optional[str]) -> Dict:
    if not path:
        return {}
    p = Path(path)
    if not p.exists():
        raise FileNotFoundError(f"Config not found: {p}")
    cfg = _read_json(p)
    if not isinstance(cfg, dict):
        raise ValueError("Config JSON must be an object.")
    return cfg

def _run_eval(dataset: str, split: str, outdir: Path, cfg: Dict, smoke: bool=False) -> Dict:
    # For Phase7b harness, we support a smoke path (no heavy downloads).
    if smoke:
        raw_pred_spans, gold_spans = _smoke_data()
        adapter_name = "smoke_adapter"
    else:
        # Placeholder for future real adapter integration via config
        raise SystemExit("Non-smoke mode not yet wired in this step. Use --smoke to validate harness.")
    # Transform -> validate
    mapped = apply_label_map(raw_pred_spans, cfg.get("label_map"), cfg.get("label_map_default"))
    valid_pred, skipped = assert_valid_spans(mapped)
    valid_gold, _ = assert_valid_spans(gold_spans)
    metrics = compute_metrics(valid_pred, valid_gold)

    # Write outputs
    outdir.mkdir(parents=True, exist_ok=True)
    _write_json(outdir / "pred_spans.jsonl", {"spans": valid_pred})
    _write_json(outdir / "metrics.json", {
        "dataset": dataset, "split": split, "adapter": adapter_name,
        "env_bypass": bool(os.getenv("DARF_BYPASS_MAP")),
        "skipped_invalid_pred_spans": skipped,
        "strict": {"f1": metrics["strict"]["f1"], "precision": metrics["strict"]["precision"], "recall": metrics["strict"]["recall"]},
        "unlabeled_boundary": metrics["unlabeled_boundary"],
        "unlabeled_text_multiset": metrics["unlabeled_text_multiset"],
        "timestamp_utc": _now_stamp(),
    })
    return metrics

def main():
    ap = argparse.ArgumentParser(description="DARF Phase7b scored evaluation runner")
    ap.add_argument("--dataset", required=True, help="Dataset name (e.g., biored)")
    ap.add_argument("--split", required=True, choices=["dev","test","train","smoke"], help="Dataset split")
    ap.add_argument("--config", required=False, help="Path to JSON config with label_map etc.")
    ap.add_argument("--outdir", required=True, help="Output directory for receipts")
    ap.add_argument("--write-docs-scoreboard", action="store_true", help="Copy scoreboard to docs/scoreboards/")
    ap.add_argument("--smoke", action="store_true", help="Run a local smoke evaluation with tiny synthetic data")
    args = ap.parse_args()

    cfg = _load_config(args.config)
    outdir = Path(args.outdir)
    dataset, split = args.dataset, args.split
    metrics = _run_eval(dataset, split, outdir, cfg, smoke=args.smoke)

    # Build a tiny scoreboard artifact (timestamped summary)
    scoreboard = {
        "dataset": dataset,
        "split": split,
        "timestamp_utc": _now_stamp(),
        "strict": metrics["strict"],
        "unlabeled_boundary": metrics["unlabeled_boundary"],
        "unlabeled_text_multiset": metrics["unlabeled_text_multiset"],
    }
    stamp = _now_stamp()
    sb_name = f"{dataset}_{split}_scoreboard_{stamp}.json"
    _write_json(outdir / "scoreboard.json", scoreboard)

    if args.write_docs_scoreboard:
        docs_path = Path("docs/scoreboards") / sb_name
        _write_json(docs_path, scoreboard)
        print(f"Wrote docs scoreboard: {docs_path}")

    print(json.dumps({"status":"ok","outdir":str(outdir),"strict_f1":scoreboard["strict"]["f1"]}, indent=2))

if __name__ == "__main__":
    main()
