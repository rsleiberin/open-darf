#!/usr/bin/env python3
import argparse
import json
import os
import glob
import time

ap = argparse.ArgumentParser()
ap.add_argument("--receipts", required=True)
ap.add_argument("--comparisons", required=True)
ap.add_argument("--out", required=True)
args = ap.parse_args()


def latest(p):
    xs = glob.glob(os.path.join(p, "*"))
    return sorted(xs)[-1] if xs else None


def load(p):
    try:
        return json.load(open(p))
    except Exception:
        return {}


sc = latest(os.path.join(args.receipts, "scierc"))
bi = latest(os.path.join(args.receipts, "biored"))
sc_s = load(os.path.join(sc, "summary.json")) if sc else {}
bi_s = load(os.path.join(bi, "summary.json")) if bi else {}
sc_cmp = load(os.path.join(args.comparisons, "scierc_compare.json"))
bi_cmp = load(os.path.join(args.comparisons, "biored_compare.json"))
md = []
md.append("# Phase 6C Benchmark Results\n")
md.append("Generated: " + time.strftime("%Y-%m-%d %H:%M:%SZ", time.gmtime()) + "\n")


def sec(title):
    md.append("\n## " + title + "\n")


def block(task, s, cmp_):
    md.append(f"**{task}**\n\n")
    m = s.get("micro", {})
    md.append(f"- Entity micro-F1: **{m.get('entity_f1',0.0):.4f}**\n")
    md.append(f"- Relation micro-F1: **{m.get('relation_f1',0.0):.4f}**\n")
    md.append(f"- Target(s): {cmp_.get('targets',{})}\n")
    md.append(f"- Pass: **{cmp_.get('pass',False)}**\n")


sec("SciERC")
block("SciERC", sc_s, sc_cmp)
sec("BioRED")
block("BioRED", bi_s, bi_cmp)
os.makedirs(os.path.dirname(args.out), exist_ok=True)
open(args.out, "w").write("".join(md))
print(json.dumps({"wrote": args.out}))
