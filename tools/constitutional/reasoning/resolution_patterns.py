from __future__ import annotations
import os, json
from dataclasses import dataclass
from typing import List, Dict, Tuple
from .conflict import PrincipleVote

def _norm(s: str) -> str:
    return " ".join(s.strip().split()).lower()

def signature(votes: List[PrincipleVote]) -> str:
    """Deterministic signature: deny|allow|abstain|pending buckets with sorted principles."""
    buckets: Dict[str, List[str]] = {"DENY": [], "ALLOW": [], "ABSTAIN": [], "PENDING": []}
    for v in votes:
        vote = (v.vote or "").strip().upper()
        vote = vote if vote in buckets else "ABSTAIN"
        buckets[vote].append(_norm(v.principle))
    parts = []
    for k in ("DENY","ALLOW","ABSTAIN","PENDING"):
        ps = "|".join(sorted(set(buckets[k])))
        parts.append(f"{k.lower()}:[{ps}]")
    return ";".join(parts)

def _path() -> str:
    return os.getenv("REASONING_PATTERN_PATH", "var/state/resolution_patterns.jsonl")

def write_pattern(votes: List[PrincipleVote], decision: str, rationale: Dict) -> str:
    """Append a captured pattern (idempotent by (sig,decision)). Returns pattern_id."""
    os.makedirs(os.path.dirname(_path()), exist_ok=True)
    sig = signature(votes)
    pid = f"pat:{sig}::{decision.strip().upper()}"
    rec = {"id": pid, "signature": sig, "decision": decision.strip().upper(), "rationale": rationale}
    # de-dup by scanning file cheaply (files are small)
    seen = set()
    if os.path.exists(_path()):
        with open(_path(), "r", encoding="utf-8") as f:
            for line in f:
                line=line.strip()
                if not line: continue
                try:
                    obj=json.loads(line)
                except Exception:
                    continue
                if obj.get("id"):
                    seen.add(obj["id"])
    if pid not in seen:
        with open(_path(), "a", encoding="utf-8") as f:
            f.write(json.dumps(rec, ensure_ascii=False) + "\n")
    return pid
