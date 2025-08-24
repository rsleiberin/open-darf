# SPDX-License-Identifier: MIT
from __future__ import annotations
import os
from typing import Tuple

from .models import TinyContentModel, TinyContextModel, ContentModel, ContextModel
from .fusion import TinyFusion, FusionClassifier


def resolve_backend() -> str:
    return os.getenv("CBDT_BACKEND", "tiny").strip().lower() or "tiny"


def get_models_from_env() -> Tuple[ContentModel, ContextModel, FusionClassifier, str]:
    """
    Returns (content_model, context_model, fusion, version_tag)
    Backends:
      - "tiny" (default): lightweight deterministic models for CI/tests.
      - "hf": placeholder for HuggingFace-backed models (not auto-enabled).
    """
    backend = resolve_backend()
    if backend == "tiny":
        return TinyContentModel(), TinyContextModel(), TinyFusion(), "tiny-0.1"
    elif backend == "hf":
        # Lazy import; never executed unless explicitly enabled.
        try:

            # NOTE: We do NOT download anything here; this is a placeholder.
            # Real wiring should be added in a separate PR with pinned checkpoints.
            raise RuntimeError(
                "CBDT_BACKEND=hf is not yet implemented in this repo. "
                "Use the default tiny backend for tests, or implement HF adapters."
            )
        except Exception as e:
            raise RuntimeError(f"HF backend unavailable: {e}")
    else:
        raise ValueError(f"Unknown CBDT_BACKEND: {backend}")
