from __future__ import annotations
import argparse, json
from pathlib import Path

def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description="Assemble Phase 7C evidence pack (markdown)")
    ap.add_argument("--receipt", required=True)
    ap.add_argument("--gallery", required=True)
    ap.add_argument("--out", required=True)
    args = ap.parse_args(argv)

    rec = json.loads(Path(args.receipt).read_text(encoding="utf-8"))
    gal = Path(args.gallery).read_text(encoding="utf-8")

    counts = rec.get("counts_tags", {})
    timing = ((rec.get("blocking_report") or {}).get("timing") or {}).get("ingest") or {}
    accepted_ct = rec.get("accepted_count", 0)
    sample_ids = rec.get("accepted_ids_sample", [])

    md = []
    md.append("# Phase 7C — Evidence Pack\n\n")
    md.append("## Summary\n")
    md.append(f"- ACCEPTABLE: {counts.get('ACCEPTABLE',0)}\n")
    md.append(f"- REJECTED: {counts.get('REJECTED',0)}\n")
    md.append(f"- PENDING: {counts.get('PENDING',0)}\n\n")
    if "ACCEPTABLE" in timing:
        t = timing["ACCEPTABLE"]
        md.append(f"Decision timing (ingest / ACCEPTABLE): p50={t.get('p50_ms',0):.3f}ms, p95={t.get('p95_ms',0):.3f}ms\n")
    if "REJECTED" in timing:
        t = timing["REJECTED"]
        md.append(f"Decision timing (ingest / REJECTED): p50={t.get('p50_ms',0):.3f}ms, p95={t.get('p95_ms',0):.3f}ms\n")
    md.append(f"\nAccepted IDs (sample): {', '.join(sample_ids) if sample_ids else '(none)'}\n\n")
    md.append("## Blocked Example Gallery (excerpt)\n\n")
    # include first ~20 lines of the gallery to keep pack compact
    lines = gal.splitlines()[:20]
    md.append("\n".join(lines) + "\n")

    outp = Path(args.out)
    outp.parent.mkdir(parents=True, exist_ok=True)
    outp.write_text("".join(md), encoding="utf-8")
    print(json.dumps({"ok": True, "out": str(outp)}))
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
