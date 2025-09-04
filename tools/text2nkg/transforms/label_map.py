"""
Label mapping transform for Text→NKG pipeline.

- Pure function (no I/O side effects)
- Optional env bypass via DARF_BYPASS_MAP
- Canonicalizes map keys for tolerant label matching
- PRESERVES bounds pulled from common aliases, then normalizes to {start,end,label}
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

_BOUND_START_KEYS = ("start","begin","offset_start","char_start")
_BOUND_END_KEYS   = ("end","stop","offset_end","char_end")
_LABEL_KEYS       = ("label","type","tag","category")

def _get_first(d: Mapping[str, object], keys) -> Optional[object]:
    for k in keys:
        if k in d:
            return d[k]
    return None

def _normalize_bounds(d: Mapping[str, object]):
    """Extract start/end from aliases without coercion; ints validated downstream."""
    start = _get_first(d, _BOUND_START_KEYS)
    end   = _get_first(d, _BOUND_END_KEYS)
    return start, end

def _extract_label(d: Mapping[str, object]):
    return _get_first(d, _LABEL_KEYS)

def apply_label_map(
    spans: Optional[Iterable[Mapping[str, object]]],
    label_map: Optional[Mapping[object, Optional[str]]] = None,
    default: Optional[str] = None,
) -> List[dict]:
    """
    Map span labels using a configurable dictionary, returning list[dict] of {start,end,label}.

    - If DARF_BYPASS_MAP is set to a truthy value, labels are preserved (no mapping),
      but output is still normalized to {start,end,label} so downstream stages can rely on shape.
    - Bounds are sourced from common aliases to avoid losing information prior to validation.
    """
    seq = list(spans or [])
    lm_in = dict(label_map or {})
    canon_map: Dict[Optional[str], Optional[str]] = {_canon_key(k): v for k, v in lm_in.items()}

    bypass = str(os.getenv("DARF_BYPASS_MAP", "")).strip() in {"1","true","TRUE","True"}

    out: List[dict] = []
    for s in seq:
        start, end = _normalize_bounds(s)
        label = _extract_label(s)

        if bypass:
            mapped = label  # preserve original label when bypassing
        else:
            if label is None:
                mapped = default
            elif label in lm_in:
                mapped = lm_in[label]
            else:
                mapped = canon_map.get(_canon_key(label), default if default is not None else label)

        out.append({"start": start, "end": end, "label": mapped})
    return out
