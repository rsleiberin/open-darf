#!/usr/bin/env python3
import json, pathlib, time, textwrap

OUT_DIR = pathlib.Path("docs/evidence/phase7e")
EX_DIR  = OUT_DIR / "enriched_examples"
OUT_DIR.mkdir(parents=True, exist_ok=True)

examples = []
for p in sorted(EX_DIR.glob("*.json")):
    try:
        data = json.loads(p.read_text(encoding="utf-8"))
        examples.append(data)
    except Exception:
        continue

pack = {
    "version": "7e_evidence_pack_v1",
    "generated_at_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
    "count": len(examples),
    "examples": [
        {
            "example_file": p.name,
            "example_id": e.get("example_id"),
            "source_path": e.get("source_path"),
            "redacted_at_utc": e.get("redacted_at_utc"),
        }
        for p, e in zip(sorted(EX_DIR.glob("*.json")), examples)
    ],
}

# Write json
(OUT_DIR / "pack.json").write_text(json.dumps(pack, indent=2), encoding="utf-8")

# Write markdown (no fenced code blocks)
lines = []
lines.append("# Phase 7E — Evidence Pack")
lines.append("")
lines.append(f"- Version: {pack['version']}")
lines.append(f"- Generated: {pack['generated_at_utc']}")
lines.append(f"- Example count: {pack['count']}")
lines.append("")
if not examples:
    lines.append("_No redacted enriched examples found in docs/evidence/phase7e/enriched_examples._")
else:
    lines.append("## Redacted Enriched Examples")
    lines.append("")
    for item in pack["examples"]:
        lines.append(f"- {item['example_file']} — id: {item['example_id']} (src: {item['source_path']})")
lines.append("")
lines.append("## Notes")
lines.append("- All examples are redacted to remove sensitive data.")
lines.append("- Reasoning enrichment is additive; no base decisions are altered.")
(OUT_DIR / "pack.md").write_text("\n".join(lines), encoding="utf-8")

print("WROTE", OUT_DIR / "pack.json")
print("WROTE", OUT_DIR / "pack.md")
