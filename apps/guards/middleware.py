from __future__ import annotations
import time
from typing import Any, Dict, Callable, List
from apps.guards import constitutional as CG


def _summarize_payload(payload: Dict[str, Any]) -> str:
    parts: List[str] = []
    for e in payload.get("entities", []):
        t = e.get("text") or e.get("label") or ""
        if t:
            parts.append(str(t))
    for r in payload.get("relations", []):
        for role in r.get("roles", []):
            t = role.get("text") or role.get("name") or ""
            if t:
                parts.append(str(t))
    for ev in payload.get("temporals", []):
        subj = ev.get("subject") or ""
        obj = ev.get("object") or ""
        if subj:
            parts.append(str(subj))
        if obj:
            parts.append(str(obj))
    return " ".join(parts)


def guarded_infer(
    text: str, infer: Callable[[str], Dict[str, Any]], stage_name: str
) -> Dict[str, Any]:
    """
    Run a model/transform behind constitutional pre/post guards.

    Decision compose rule:
      - DENY if any stage (pre, payload, post) is DENY
      - ALLOW if all three are ALLOW
      - otherwise INDETERMINATE
    """
    trace: List[Dict[str, Any]] = []

    # Pre-check on raw input
    pre = CG.evaluate({"text": text})
    trace.append(
        {
            "stage": f"{stage_name}:pre",
            "decision": pre.decision,
            "reason_code": pre.reason_code,
        }
    )
    if pre.decision == "DENY":
        return {
            "decision": "DENY",
            "reason_code": pre.reason_code,
            "entities": [],
            "relations": [],
            "temporals": [],
            "provenance": {"stage": stage_name, "middleware": True},
            "guard_trace": trace,
            "guard_overhead_ms": 0.0,
        }

    # Inference
    t0 = time.perf_counter()
    payload = infer(text) or {}
    payload.setdefault("entities", [])
    payload.setdefault("relations", [])
    payload.setdefault("temporals", [])

    # Post-check on summarized output (neutral if empty)
    summary = _summarize_payload(payload)
    if summary.strip():
        post = CG.evaluate({"text": summary})
        post_decision, post_reason = post.decision, post.reason_code
    else:
        post_decision, post_reason = "INDETERMINATE", "empty_summary"

    dt_ms = (time.perf_counter() - t0) * 1000.0
    trace.append(
        {
            "stage": f"{stage_name}:post",
            "decision": post_decision,
            "reason_code": post_reason,
        }
    )

    # Compose final decision explicitly
    payload_decision = payload.get("decision", "ALLOW")
    stages = (pre.decision, payload_decision, post_decision)
    if "DENY" in stages:
        final = "DENY"
    elif all(d == "ALLOW" for d in stages):
        final = "ALLOW"
    else:
        final = "INDETERMINATE"

    # Attach standardized fields
    payload["decision"] = final
    payload["reason_code"] = payload.get("reason_code", "ok")
    payload["guard_trace"] = trace
    payload["guard_overhead_ms"] = dt_ms
    prov = payload.setdefault("provenance", {})
    prov["middleware"] = True
    prov["mw_stage"] = stage_name
    return payload
