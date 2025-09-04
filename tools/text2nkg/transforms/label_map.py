"""
Label mapping transform for Text→NKG pipeline.

- Pure function (no I/O side effects)
- Optional env bypass via DARF_BYPASS_MAP
- Canonicalizes map keys: lowercase and strip non-alnum
- Preserves input order; returns list[dict] with keys: start, end, label
"""
from __future__ import annotations
import os
import re
from typing import Dict, Iterable, List, Mapping, Optional

_CANON = re.compile(r"[^a-z0-9]+")

def _canon_key(s: Optional[object]) -> Optional[str]:
    if s is None:
        return None
    return _CANON.sub("", str(s).lower())

def apply_label_map(
    spans: Optional[Iterable[Mapping[str, object]]],
    label_map: Optional[Mapping[object, Optional[str]]] = None,
    default: Optional[str] = None,
) -> List[dict]:
    """
    Map span labels using a configurable dictionary.

    Behavior:
      - If DARF_BYPASS_MAP in {"1","true","TRUE","True"} → return spans unchanged (normalized keys only).
      - Canonicalize label_map keys to allow tolerant matching.
      - Preserve input order; do not coerce bounds (validator handles later).
    """
    seq = list(spans or [])

    # Bypass entirely if env set
    if str(os.getenv("DARF_BYPASS_MAP", "")).strip() in {"1", "true", "TRUE", "True"}:
        out: List[dict] = []
        for s in seq:
            start = s.get("start")
            end = s.get("end")
            label = s.get("label")
            out.append({"start": start, "end": end, "label": label})
        return out

    lm_in = dict(label_map or {})
    canon_map: Dict[Optional[str], Optional[str]] = {_canon_key(k): v for k, v in lm_in.items()}

    out: List[dict] = []
    for s in seq:
        start = s.get("start")
        end = s.get("end")
        label = s.get("label")
        if label is None:
            label = s.get("type") or s.get("tag") or s.get("category")

        if label is None:
            mapped = default
        else:
            if label in lm_in:
                mapped = lm_in[label]
            else:
                mapped = canon_map.get(_canon_key(label), default if default is not None else label)

        out.append({"start": start, "end": end, "label": mapped})
    return out
