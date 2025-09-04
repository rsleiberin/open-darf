from __future__ import annotations
import argparse
import json
import os
import shutil
import time
from pathlib import Path
from typing import Dict, List, Mapping, Optional, Tuple

from tools.text2nkg.transforms.label_map import apply_label_map
from tools.text2nkg.emit_nkg import assert_valid_spans
from tools.text2nkg.pipeline import compute_metrics

# ----------------------------
# Helpers (defined BEFORE main)
# ----------------------------

def _now_stamp() -> str:
    return time.strftime("%Y%m%d-%H%M%S", time.gmtime())

def _read_json(path: Path) -> Dict:
    with open(path, "r", encoding="utf-8") as f:
        return json.load(f)

def _write_json(path: Path, obj) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with open(path, "w", encoding="utf-8") as f:
        json.dump(obj, f, ensure_ascii=False, indent=2, sort_keys=True)

def _read_spans_any(path: Path) -> List[dict]:
    """
    Read spans from:
      - JSON object with key "spans": {"spans":[...]}
      - JSON array: [ {...}, {...} ]
      - JSONL: one JSON span per line
    Returns list[dict].
    """
    txt = path.read_text(encoding="utf-8").strip()
    if not txt:
        return []
    first = txt.lstrip()[:1]
    try:
        if first == "{":
            obj = json.loads(txt)
            if isinstance(obj, dict) and "spans" in obj:
                spans = obj.get("spans") or []
                return list(spans)
            return []
        elif first == "[":
            arr = json.loads(txt)
            if isinstance(arr, list):
                return list(arr)
            return []
        else:
            # JSONL
            spans: List[dict] = []
            for line in txt.splitlines():
                line = line.strip()
                if not line:
                    continue
                spans.append(json.loads(line))
            return spans
    except Exception:
        return []

def _load_real_paths(pred_path: str, gold_path: str) -> Tuple[List[dict], List[dict]]:
    pp, gp = Path(pred_path), Path(gold_path)
    if not pp.exists():
        raise FileNotFoundError(f"Pred path missing: {pp}")
    if not gp.exists():
        raise FileNotFoundError(f"Gold path missing: {gp}")
    pred = _read_spans_any(pp)
    gold = _read_spans_any(gp)
    return pred, gold

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

def _run_eval(
    dataset: str,
    split: str,
    outdir: Path,
    cfg: Dict,
    smoke: bool = False,
    pred_path: str | None = None,
    gold_path: str | None = None,
) -> Dict:
    # Obtain raw preds/gold
    if smoke:
        raw_pred_spans, gold_spans = _smoke_data()
        adapter_name = "smoke_adapter"
    else:
        if pred_path and gold_path:
            raw_pred_spans, gold_spans = _load_real_paths(pred_path, gold_path)
            adapter_name = "from_paths"
        else:
            raise SystemExit("Provide --pred-path and --gold-path (or use --smoke).")

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

# -----------
# Entry point
# -----------

def main():
    ap = argparse.ArgumentParser(description="DARF Phase7b scored evaluation runner")
    ap.add_argument("--dataset", required=True, help="Dataset name (e.g., biored)")
    ap.add_argument("--split", required=True, choices=["dev","test","train","smoke"], help="Dataset split")
    ap.add_argument("--config", required=False, help="Path to JSON config with label_map etc.")
    ap.add_argument("--outdir", required=True, help="Output directory for receipts")
    ap.add_argument("--write-docs-scoreboard", dest="write_docs_scoreboard", action="store_true", help="Copy scoreboard to docs/scoreboards/")
    ap.add_argument("--smoke", action="store_true", help="Run a local smoke evaluation with tiny synthetic data")
    ap.add_argument("--pred-path", required=False, help="Path to predicted spans (JSON/JSONL)")
    ap.add_argument("--gold-path", required=False, help="Path to gold spans (JSON/JSONL)")
    args = ap.parse_args()

    cfg = _load_config(args.config)
    outdir = Path(args.outdir)
    dataset, split = args.dataset, args.split

    metrics = _run_eval(dataset, split, outdir, cfg, smoke=args.smoke, pred_path=args.pred_path, gold_path=args.gold_path)

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
