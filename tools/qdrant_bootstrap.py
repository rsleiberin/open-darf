from __future__ import annotations
from dataclasses import dataclass
from typing import Any, Dict, Tuple


@dataclass
class VectorConfig:
    size: int = 1024
    distance: str = "Cosine"  # Accept: Cosine | Dot | Euclid


def collection_config(
    name: str = "anchors", *, vec: VectorConfig = VectorConfig()
) -> Dict[str, Any]:
    """
    Declarative config dict for a Qdrant collection. Pure function.
    """
    return {
        "name": name,
        "vectors": {"size": vec.size, "distance": vec.distance},
        "on_disk": True,
        "optimizers_config": {"default_segment_number": 2},
        # Add payload schema later if/when we lock fields
    }


def ensure_collection(
    client: Any, name: str = "anchors", *, vec: VectorConfig = VectorConfig()
) -> Tuple[bool, Dict[str, Any]]:
    """
    Idempotently ensure a collection exists using an injected client.
    Expected client minimal surface:
      - get_collection(name) -> dict     (raises KeyError if not found)
      - create_collection(collection_name=<str>, vectors_config=<dict>) -> any
    Returns (created, summary_dict).
    """
    try:
        existing = client.get_collection(name)
        cfg = existing.get("config") if isinstance(existing, dict) else None
        return (False, {"ok": True, "name": name, "existing": True, "config": cfg})
    except KeyError:
        pass

    vectors_cfg = {"size": vec.size, "distance": vec.distance}
    client.create_collection(collection_name=name, vectors_config=vectors_cfg)
    return (
        True,
        {"ok": True, "name": name, "created": True, "config": {"vectors": vectors_cfg}},
    )
