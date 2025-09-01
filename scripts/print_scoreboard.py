#!/usr/bin/env python3
import json
import sys
from pathlib import Path

p = Path("var/reports/phase6c/gates.json")
if not p.exists():
    print("gates.json not found at", p, file=sys.stderr)
    sys.exit(2)

g = json.loads(p.read_text(encoding="utf-8"))


def row(name, d):
    parts = []
    if "entity_f1" in d:
        parts.append(f"entity F1: {d['entity_f1']:.4f}")
    if "relation_f1" in d:
        parts.append(f"relation F1: {d['relation_f1']:.4f}")
    if "precision" in d and "recall" in d:
        parts.append(f"P/R: {d['precision']:.4f}/{d['recall']:.4f}")
    print(f"- {name}: " + ("; ".join(parts) if parts else "(no metrics)"))


print("=== Scoreboard (from gates.json) ===")
if "scierc" in g:
    row("SciERC", g["scierc"])
else:
    print("- SciERC: (missing)")
if "biored" in g:
    row("BioRED", g["biored"])
else:
    print("- BioRED: (missing)")
