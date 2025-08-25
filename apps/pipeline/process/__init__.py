"""Downstream processing stages (e.g., CBDT bias detector)."""

from typing import Dict, Any


def run_bias_checks(text: str) -> Dict[str, Any]:
    """Return a minimal bias report dict. Stub returns neutral."""
    return {"cbdt": {"score": 0.0, "notes": "stub"}}
