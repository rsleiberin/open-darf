#!/usr/bin/env python3
import json, os, glob, hashlib, time, statistics

def load_json(path):
    try:
        with open(path, "r", encoding="utf-8") as f:
            return json.load(f)
    except Exception as e:
        return {"_error": str(e), "_path": path}

def sha256sum(path):
    try:
        h = hashlib.sha256()
        with open(path, "rb") as f:
            for chunk in iter(lambda: f.read(65536), b""):
                h.update(chunk)
        return h.hexdigest()
    except Exception:
        return None

def main():
    # Inputs
    roots = [
        "open-darf/var/receipts/open-darf",     # oneclick receipts
        "var/receipts/open-darf"                # fallback (if any)
    ]
    tar_roots = [
        "open-darf",                             # open-darf report tarballs
        "."                                      # repo root tarballs
    ]

    receipts = []
    for r in roots:
        receipts.extend(sorted(glob.glob(os.path.join(r, "oneclick_*.json"))))

    tarballs = []
    for r in tar_roots:
        tarballs.extend(sorted(glob.glob(os.path.join(r, "open-darf-report-*.tar.gz"))))

    # Parse receipts
    parsed = [load_json(p) | {"_path": p} for p in receipts]
    count = len(parsed)
    by_wsl = {"wsl": sum(1 for x in parsed if x.get("is_wsl")==1),
              "native": sum(1 for x in parsed if x.get("is_wsl")==0)}
    install_ok = sum(1 for x in parsed if x.get("steps",{}).get("install_rc")==0)
    run_min_ok = sum(1 for x in parsed if x.get("steps",{}).get("run_minimal_rc")==0)
    evidence_ok = sum(1 for x in parsed if x.get("steps",{}).get("evidence_rc")==0)

    # Simple timing proxies unavailable; compute coverage stats
    summary = {
        "timestamp": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "receipts": {
            "count": count,
            "by_wsl": by_wsl,
            "install_ok": install_ok,
            "run_minimal_ok": run_min_ok,
            "evidence_ok": evidence_ok,
        },
        "tarballs": {
            "count": len(tarballs),
            "items": [
                {"path": t, "sha256": sha256sum(t), "size_bytes": os.path.getsize(t)} 
                for t in tarballs
            ]
        },
        "samples": [
            {
                "host": x.get("host"),
                "distro": x.get("distro"),
                "kernel": x.get("kernel"),
                "is_wsl": x.get("is_wsl"),
                "gpu_info": x.get("gpu_info"),
                "status": x.get("status"),
                "reason": x.get("reason"),
                "_path": x.get("_path")
            } for x in parsed[:10]  # cap sample list
        ]
    }

    outdir = "var/reports/phase7s"
    os.makedirs(outdir, exist_ok=True)
    with open(os.path.join(outdir, "validation_summary.json"), "w", encoding="utf-8") as f:
        json.dump(summary, f, indent=2)

    # Markdown companion
    md = []
    md.append("# Phase 7S — Validation Evidence Summary\n")
    md.append(f"- Generated: {summary['timestamp']}")
    md.append(f"- Receipts: {summary['receipts']['count']}")
    md.append(f"- WSL vs Native: {summary['receipts']['by_wsl']}")
    md.append(f"- Steps OK — install:{install_ok} run_minimal:{run_min_ok} evidence:{evidence_ok}\n")
    md.append("## Tarballs\n")
    for t in summary["tarballs"]["items"]:
        md.append(f"- `{t['path']}` — {t['size_bytes']} bytes — sha256:{t['sha256']}")
    md.append("\n## Sample Receipts (up to 10)\n")
    for s in summary["samples"]:
        md.append(f"- host:{s['host']} wsl:{s['is_wsl']} status:{s['status']} reason:{s['reason']}  \n  {s['_path']}  \n  {s['distro']} | {s['kernel']}  \n  GPU:{s['gpu_info']}")
    with open(os.path.join(outdir, "validation_summary.md"), "w", encoding="utf-8") as f:
        f.write("\n".join(md) + "\n")

    print("[ok] Wrote var/reports/phase7s/validation_summary.{json,md}")

if __name__ == "__main__":
    main()
