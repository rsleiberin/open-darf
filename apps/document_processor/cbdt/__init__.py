# SPDX-License-Identifier: MIT
"""
CBDT (Contextual Bi-directional Dual Transformer) module boundaries.

This package defines DI-friendly interfaces for:
- ContentModel: encodes document text into features.
- ContextModel: encodes citation/methodology context into features.
- FusionClassifier: combines both feature sets to predict bias categories.
- CBDTBiasDetector: orchestration layer used by the pipeline.

The default implementations here are LIGHTWEIGHT FAKE MODELS for unit tests
and local runs without heavyweight checkpoints. In production, plug in real
models (e.g., HuggingFace) by implementing the same interfaces.
"""
from .detector import CBDTBiasDetector, BiasCategory, CBDTConfig
from .models import ContentModel, ContextModel
from .fusion import FusionClassifier

__all__ = [
    "CBDTBiasDetector",
    "BiasCategory",
    "CBDTConfig",
    "ContentModel",
    "ContextModel",
    "FusionClassifier",
]
