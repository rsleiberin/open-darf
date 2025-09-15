#!/usr/bin/env python3
import json, os, glob, hashlib, time, math, collections

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

def wilson(successes, n, z=1.96):
    if n <= 0:
        return {"p": None, "lo": None, "hi": None, "n": 0, "k": 0}
    p = successes / n
    denom = 1 + z*z/n
    center = p + z*z/(2*n)
    pm = z * math.sqrt((p*(1-p) + z*z/(4*n))/n)
    lo = (center - pm)/denom
    hi = (center + pm)/denom
    return {"p": p, "lo": max(0.0, lo), "hi": min(1.0, hi), "n": n, "k": successes}

def main():
    roots = [
        "open-darf/var/receipts/open-darf",
        "var/receipts/open-darf"
    ]
    tar_roots = ["open-darf", "."]

    receipts = []
    for r in roots:
        receipts.extend(sorted(glob.glob(os.path.join(r, "oneclick_*.json"))))

    tarballs = []
    for r in tar_roots:
        tarballs.extend(sorted(glob.glob(os.path.join(r, "open-darf-report-*.tar.gz"))))

    parsed = [({**load_json(p), "_path": p}) for p in receipts]
    n = len(parsed)

    install_ok = sum(1 for x in parsed if x.get("steps",{}).get("install_rc")==0)
    run_ok     = sum(1 for x in parsed if x.get("steps",{}).get("run_minimal_rc")==0)
    ev_ok      = sum(1 for x in parsed if x.get("steps",{}).get("evidence_rc")==0)

    by_wsl = {"wsl": sum(1 for x in parsed if x.get("is_wsl")==1),
              "native": sum(1 for x in parsed if x.get("is_wsl")==0)}

    # Optional: simple GPU name frequency
    gpu_counts = collections.Counter()
    for x in parsed:
        gi = (x.get("gpu_info") or "").split(",")[0].strip()
        if gi:
            gpu_counts[gi] += 1

    summary = {
        "timestamp": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "receipts": {
            "count": n,
            "by_wsl": by_wsl,
            "install_ok": install_ok,
            "run_minimal_ok": run_ok,
            "evidence_ok": ev_ok,
            "install_ok_ci95": wilson(install_ok, n),
            "run_minimal_ok_ci95": wilson(run_ok, n),
            "evidence_ok_ci95": wilson(ev_ok, n),
            "gpu_frequency": gpu_counts.most_common(10)
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
            } for x in parsed[:10]
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
    md.append(f"- Receipts: {n}")
    md.append(f"- WSL vs Native: {by_wsl}")
    def pct(ci):
        if ci["p"] is None: return "n/a"
        return f"{ci['p']*100:.1f}% (95% CI {ci['lo']*100:.1f}–{ci['hi']*100:.1f}%)"
    md.append(f"- Install success: {install_ok}/{n} = {pct(summary['receipts']['install_ok_ci95'])}")
    md.append(f"- Minimal run success: {run_ok}/{n} = {pct(summary['receipts']['run_minimal_ok_ci95'])}")
    md.append(f"- Evidence packaging success: {ev_ok}/{n} = {pct(summary['receipts']['evidence_ok_ci95'])}\n")
    if gpu_counts:
        md.append("## GPU Frequency (Top)\n")
        for name, c in gpu_counts.most_common(10):
            md.append(f"- {name}: {c}")
        md.append("")
    md.append("## Tarballs\n")
    for t in summary["tarballs"]["items"]:
        md.append(f"- `{t['path']}` — {t['size_bytes']} bytes — sha256:{t['sha256']}")
    md.append("\n## Sample Receipts (up to 10)\n")
    for s in summary["samples"]:
        md.append(f"- host:{s['host']} wsl:{s['is_wsl']} status:{s['status']} reason:{s['reason']}  ")
        md.append(f"  {s['_path']}  ")
        md.append(f"  {s['distro']} | {s['kernel']}  ")
        md.append(f"  GPU:{s['gpu_info']}")
    with open(os.path.join(outdir, "validation_summary.md"), "w", encoding="utf-8") as f:
        f.write("\n".join(md) + "\n")

    print("[ok] Wrote var/reports/phase7s/validation_summary.{json,md} with Wilson CIs")

if __name__ == "__main__":
    main()
