import time
from typing import Dict, Any, Tuple, List

ALLOW="ALLOW"; DENY="DENY"; INDET="INDETERMINATE"

def decide(action: str, context: Dict[str, Any]) -> Tuple[str, List[str], float, float]:
    """
    Returns: (state, principles_applied, confidence, elapsed_us)
    - principles_applied includes short explanations prefixed 'exp:'
    """
    t0 = time.perf_counter()
    txt = (context.get("text") or context.get("sentence") or "").strip()
    length = len(txt)
    if length == 0:
        state = INDET
        conf = 0.25
        principles = ["exp:empty-input→indeterminate"]
    else:
        # Deterministic demo policy: allow, confidence scales with length up to 256 chars
        conf = min(1.0, max(0.3, length / 256.0))
        state = ALLOW
        principles = [f"exp:len={length}→allow(conf≈{conf:.2f})"]
    elapsed_us = (time.perf_counter() - t0) * 1e6
    return state, principles, conf, elapsed_us
