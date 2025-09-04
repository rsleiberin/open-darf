from __future__ import annotations
import argparse, json, subprocess
from pathlib import Path
from typing import Dict, Iterable

ALLOWED = {"ACCEPTABLE","REJECTED","PENDING"}

def load_jsonl(p: Path):
    with p.open("r", encoding="utf-8") as fh:
        for line in fh:
            line = line.strip()
            if not line: 
                continue
            yield json.loads(line)

def count_tags(tags_path: Path) -> Dict[str,int]:
    c = {"ACCEPTABLE":0,"REJECTED":0,"PENDING":0,"UNKNOWN":0}
    for t in load_jsonl(tags_path):
        d = str(t.get("decision","")).upper()
        if d in ALLOWED:
            c[d] += 1
        else:
            c["UNKNOWN"] += 1
    return c

def list_ids(p: Path) -> list:
    return [str(x.get("id")) for x in load_jsonl(p)]

def git_meta() -> Dict[str,str]:
    def run(cmd: list) -> str:
        try:
            return subprocess.check_output(cmd, text=True).strip()
        except Exception:
            return ""
    return {
        "branch": run(["git","rev-parse","--abbrev-ref","HEAD"]),
        "commit": run(["git","rev-parse","--short","HEAD"]),
        "remote": run(["git","remote","get-url","origin"]),
    }

def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description="Write Phase 7C demo receipt")
    ap.add_argument("--demo-dir", required=True, help="Path to demo directory")
    ap.add_argument("--report", required=False, help="Path to reporter JSON (optional)")
    ap.add_argument("--out", required=True, help="Output receipt JSON path")
    args = ap.parse_args(argv)

    base = Path(args.demo_dir)
    tags = base / "tags.jsonl"
    accepted = base / "accepted.jsonl"
    report = Path(args.report) if args.report else (base / "report_blocking.json")

    meta = git_meta()
    counts = count_tags(tags) if tags.exists() else {}
    accepted_ids = list_ids(accepted) if accepted.exists() else []
    rep = json.loads(report.read_text(encoding="utf-8")) if report.exists() else {}

    # Consistency check: accepted IDs ⊆ ACCEPTABLE tags (best-effort)
    ok_subset = True
    tag_ok_ids = set()
    try:
        tag_ok_ids = {t["id"] for t in (json.loads(line) for line in tags.read_text(encoding="utf-8").splitlines() if line.strip()) if str(t.get("decision","")).upper()=="ACCEPTABLE"}
        ok_subset = set(accepted_ids).issubset(tag_ok_ids)
    except Exception:
        ok_subset = False

    receipt = {
        "phase": "7C",
        "demo_dir": str(base),
        "git": meta,
        "counts_tags": counts,
        "accepted_count": len(accepted_ids),
        "accepted_ids_sample": accepted_ids[:10],
        "blocking_report": rep,
        "consistency": {"accepted_subset_of_tags": ok_subset},
    }
    Path(args.out).parent.mkdir(parents=True, exist_ok=True)
    Path(args.out).write_text(json.dumps(receipt, ensure_ascii=False, indent=2), encoding="utf-8")
    print(json.dumps({"ok": True, "out": str(args.out)}, ensure_ascii=False))
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
