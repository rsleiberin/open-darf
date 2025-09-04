from __future__ import annotations
import json, glob, os, time
from pathlib import Path
from typing import Dict, Any, List

from .engine import ExplanationEngine
from .context import ReasoningInput
from .quality import quality_score

ROOT = Path(__file__).resolve().parents[3]
AUDIT_DIR = ROOT / "docs" / "audit"
EVID_DIR  = ROOT / "docs" / "evidence" / "phase7d"
EVID_DIR.mkdir(parents=True, exist_ok=True)

def _read_json(p: Path) -> Any:
    try:
        return json.loads(p.read_text(encoding="utf-8"))
    except Exception:
        return None

def collect_receipts() -> Dict[str, Any]:
    out: Dict[str, Any] = {"receipts": []}
    for pat in [
        "phase7d_reasoning_perf_*.json",
        "phase7d_group*_progress_*.json",
        "phase7d_group4_completion_*.json"
    ]:
        for f in sorted(AUDIT_DIR.glob(pat)):
            data = _read_json(f)
            if data is not None:
                out["receipts"].append({"file": f.name, "data": data})
    return out

def demo_explanations() -> Dict[str, Any]:
    eng = ExplanationEngine()
    demos: List[Dict[str, Any]] = []
    cases = [
        dict(id="demo:allow",   decision="ACCEPTABLE", principles=["sovereignty","safety"], rationale="allow provenance-verified", evidence_ids=["doc:demo1"]),
        dict(id="demo:reject",  decision="REJECTED",   principles=["fail-closed","safety"], rationale="empty text",               evidence_ids=["doc:demo2"]),
        dict(id="demo:pending", decision="PENDING",    principles=["transparency"],           rationale="insufficient evidence",    evidence_ids=["doc:demo3"]),
    ]
    for c in cases:
        rin = ReasoningInput(decision=c["decision"], principles=c["principles"], rationale=c["rationale"], evidence_ids=c["evidence_ids"])
        exp = eng.explain(rin, precedents=())
        demos.append({
            "id": c["id"],
            "explanation": {
                "decision": exp.decision,
                "applied_principles": list(exp.applied_principles),
                "reasoning_path": list(exp.reasoning_path),
                "cited_precedents": list(exp.cited_precedents),
                "meta": {"confidence": exp.meta.confidence, "uncertainty_note": exp.meta.uncertainty_note},
                "quality": quality_score(exp),
            }
        })
    return {"explanations": demos}

def _patterns_summary():
    import os, json
    p = (Path(__file__).resolve().parents[3] / 'var' / 'state' / 'resolution_patterns.jsonl')
    if not p.exists():
        return {"count": 0}
    cnt=0
    sigs=set()
    for line in p.read_text(encoding='utf-8').splitlines():
        line=line.strip()
        if not line:
            continue
        try:
            obj=json.loads(line)
        except Exception:
            continue
        cnt += 1
        sigs.add(obj.get('signature',''))
    return {"count": cnt, "unique_signatures": len([s for s in sigs if s])}


def main():
    bundle = {
        "generated_at": time.time(),
        "summary": "Phase 7D — Constitutional Reasoning Evidence Pack",
        "bundle_version": 1,
        "artifacts": collect_receipts(),
        "patterns": _patterns_summary(),
        "demos": demo_explanations(),
    }
    json_out = EVID_DIR / "phase7d_evidence_bundle.json"
    json_out.write_text(json.dumps(bundle, ensure_ascii=False, indent=2), encoding="utf-8")

    # Compose a markdown overview
    md = []
    md.append("# Phase 7D — Technical Evidence Pack\n")
    md.append("## Overview\nDeterministic reasoning engine with audit enrichment, precedent tracking, conflict resolution, and performance receipts.\n")
    md.append("## Performance (from receipts)\n")
    for r in bundle["artifacts"]["receipts"]:
        if "reasoning_perf" in r["file"]:
            pct = r["data"].get("percentiles_ns") or r["data"].get("percentiles") or r["data"].get("percentilesNs") or {}
            md.append(f"- `{r['file']}` p50={pct.get('p50','?')}ns p95={pct.get('p95','?')}ns p99={pct.get('p99','?')}ns\n")
    md.append("\n## Explanation Trails (demos)\n")
    for d in bundle["demos"]["explanations"]:
        e = d["explanation"]
        md.append(f"### {d['id']}\n")
        md.append(f"- decision: **{e['decision']}**\n")
        md.append(f"- principles: {', '.join(e['applied_principles'])}\n")
        md.append(f"- rationale: {', '.join(e['reasoning_path'])}\n")
        md.append(f"- cited_precedents: {', '.join(e['cited_precedents']) or '—'}\n")
        md.append(f"- confidence: {e['meta']['confidence']:.2f} | quality: {e['quality']['score']:.2f}\n")
    md_out = EVID_DIR / "phase7d_evidence_pack.md"
    md_out.write_text("".join(md), encoding="utf-8")

    print(str(json_out))
    print(str(md_out))

if __name__ == "__main__":
    main()
