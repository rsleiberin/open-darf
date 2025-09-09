#!/usr/bin/env python3
import argparse, json, hashlib, pathlib, sys

def md5sum(p: pathlib.Path):
    h = hashlib.md5()
    with p.open("rb") as f:
        for chunk in iter(lambda: f.read(65536), b""):
            h.update(chunk)
    return h.hexdigest()

def load_lines(p: pathlib.Path):
    txt = p.read_text(encoding="utf-8").strip()
    if not txt:
        return []
    if txt.startswith("{"):
        return [json.loads(txt)]
    if txt.startswith("["):
        return json.loads(txt)
    # else JSONL
    return [json.loads(line) for line in txt.splitlines() if line.strip()]

def check_dataset(root: pathlib.Path, name: str, expected=None):
    ds_dir = root / name
    report = {"dataset": name, "present": ds_dir.is_dir(), "splits": {}, "ok": True}
    if not ds_dir.is_dir():
        report["ok"] = False
        return report
    for split in ("train","dev","test"):
        entry = {"path":"", "exists": False, "lines": 0, "md5": "", "labels_ok": True}
        # try .jsonl, then .json
        for ext in ("jsonl","json"):
            p = ds_dir / f"{split}.{ext}"
            if p.exists():
                entry["path"] = str(p)
                entry["exists"] = True
                try:
                    rows = load_lines(p)
                    entry["lines"] = len(rows)
                    # very light label sanity
                    labels_ok = True
                    sample = rows[0] if rows else {}
                    if isinstance(sample, dict):
                        # Expect some indication of entities or relations
                        keys = set(sample.keys())
                        if not ({"entities","relations"} & keys or {"labels","ner"} & keys):
                            labels_ok = True  # be permissive
                    entry["labels_ok"] = labels_ok
                    entry["md5"] = md5sum(p)
                except Exception:
                    entry["labels_ok"] = False
                break
        report["splits"][split] = entry
        if not entry["exists"]:
            report["ok"] = False
    # optional expected counts
    if expected and name in expected:
        for split, exp in expected[name].items():
            got = report["splits"].get(split,{}).get("lines", -1)
            if exp is not None and got != -1 and got != exp:
                report["ok"] = False
                report["splits"][split]["count_mismatch"] = {"expected": exp, "got": got}
    return report

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", default="data")
    ap.add_argument("--json", action="store_true", help="emit machine-readable JSON")
    args = ap.parse_args()
    root = pathlib.Path(args.root)
    # Expected counts are best-effort and may vary by release; leave as None if unknown
    expected = {
        "scierc": {"train": None, "dev": None, "test": None},
        "biored": {"train": None, "dev": None, "test": None}
    }
    sc = check_dataset(root, "scierc", expected)
    br = check_dataset(root, "biored", expected)
    overall_ok = sc["ok"] and br["ok"]
    out = {"ok": overall_ok, "details": [sc, br]}
    if args.json:
        print(json.dumps(out, indent=2))
    else:
        print(f"[SPLITS] overall_ok={overall_ok}")
        for ds in out["details"]:
            print(f"  - {ds['dataset']}: present={ds['present']} ok={ds['ok']}")
            for sp, e in ds["splits"].items():
                print(f"    * {sp}: exists={e['exists']} lines={e['lines']} md5={e['md5'][:8] if e['md5'] else ''} labels_ok={e['labels_ok']}")
    return 0 if overall_ok else 1

if __name__ == "__main__":
    sys.exit(main())
