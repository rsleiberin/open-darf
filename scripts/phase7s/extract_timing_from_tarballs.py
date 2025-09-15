#!/usr/bin/env python3
import json, os, glob, tarfile, time, math

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

def read_member_json(tar_path, member_name):
    try:
        with tarfile.open(tar_path, "r:gz") as tf:
            # Accept exact, './'-prefixed, or nested paths matching the basename
            cand = None
            base = member_name.rsplit('/', 1)[-1]
            for m in tf.getmembers():
                name = m.name
                # Normalize leading './'
                if name.startswith("./"):
                    name_norm = name[2:]
                else:
                    name_norm = name
                # Match basename or full exact
                if name_norm == member_name or name_norm.endswith("/" + base) or name_norm == base:
                    cand = m
                    break
            if cand is None:
                return None
            f = tf.extractfile(cand)
            if f is None:
                return None
            return json.loads(f.read().decode("utf-8"))
    except Exception:
        return None

def main():
    # discover tarballs
    tars = []
    for root in ["open-darf", "."]:
        tars.extend(sorted(glob.glob(os.path.join(root, "open-darf-report-*.tar.gz"))))
    records = []
    for t in tars:
        tp = read_member_json(t, "timing_probe.json")
        if tp:
            rec = {
                "path": t,
                "clock_resolution_s": tp.get("clock",{}).get("resolution_s"),
                "micro_min_delta_s": tp.get("microbench",{}).get("min_delta_s"),
                "micro_median_min_delta_s": tp.get("microbench",{}).get("median_min_delta_s"),
                "sub_ms_supported": tp.get("sub_ms_supported")
            }
            records.append(rec)

    n = len(records)
    subms = sum(1 for r in records if r.get("sub_ms_supported") is True)
    # simple stats helpers
    def stat(vals):
        vals = [v for v in vals if isinstance(v, (int,float))]
        if not vals:
            return None
        return {"min": min(vals), "median": sorted(vals)[len(vals)//2], "max": max(vals)}
    res_stats = stat([r.get("clock_resolution_s") for r in records])
    min_delta_stats = stat([r.get("micro_min_delta_s") for r in records])

    summary = {
        "timestamp": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "samples": n,
        "sub_ms": {"k": subms, "n": n, "ci95": wilson(subms, n)},
        "clock_resolution_s_stats": res_stats,
        "micro_min_delta_s_stats": min_delta_stats,
        "records": records[:20]  # cap
    }

    outdir = "var/reports/phase7s"
    os.makedirs(outdir, exist_ok=True)
    with open(os.path.join(outdir, "timing_summary.json"), "w", encoding="utf-8") as f:
        json.dump(summary, f, indent=2)

    # markdown
    def pct(ci):
        if ci["p"] is None: return "n/a"
        return f"{ci['p']*100:.1f}% (95% CI {ci['lo']*100:.1f}–{ci['hi']*100:.1f}%)"
    md = []
    md.append("# Phase 7S — Timing Probe Summary\n")
    md.append(f"- Generated: {summary['timestamp']}")
    md.append(f"- Samples with timing_probe.json: {n}")
    md.append(f"- Sub-ms supported: {subms}/{n} = {pct(summary['sub_ms']['ci95'])}\n")
    md.append("## Stats\n")
    md.append(f"- clock_resolution_s (min/median/max): {res_stats}")
    md.append(f"- micro_min_delta_s  (min/median/max): {min_delta_stats}\n")
    md.append("## Sample Records\n")
    for r in records[:10]:
        md.append(f"- {r['path']}  ")
        md.append(f"  resolution_s={r['clock_resolution_s']}  micro_min_delta_s={r['micro_min_delta_s']}  sub_ms={r['sub_ms_supported']}")
    with open(os.path.join(outdir, "timing_summary.md"), "w", encoding="utf-8") as f:
        f.write("\n".join(md) + "\n")

    print("[ok] Wrote var/reports/phase7s/timing_summary.{json,md}")

if __name__ == "__main__":
    main()
