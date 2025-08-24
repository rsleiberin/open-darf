# SPDX-License-Identifier: MIT
from __future__ import annotations
from dataclasses import dataclass
from typing import Any, Dict, Iterable, List, Optional, Tuple
import importlib
import os


@dataclass(frozen=True)
class QdrantConfig:
    url: str
    api_key: Optional[str] = None
    collection: str = "anchors"
    vector_size: int = 384
    distance: str = "Cosine"  # "Cosine" | "Euclid" | "Dot"


class QdrantWrapper:
    """
    Thin DI-friendly wrapper around qdrant-client. In tests we inject a fake.
    """

    def __init__(self, client: Any):
        self._client = client

    @classmethod
    def from_env(cls) -> "QdrantWrapper":
        # Lazy import so unit tests don't require the package.
        qdrant_mod = importlib.import_module("qdrant_client")
        url = os.getenv("QDRANT_URL", "http://localhost:6333")
        api_key = os.getenv("QDRANT_API_KEY")
        client = qdrant_mod.QdrantClient(url=url, api_key=api_key)
        return cls(client)

    def ensure_collection(self, cfg: QdrantConfig) -> None:
        """Idempotent ensure: create if missing, otherwise no-op."""
        try:
            info = self._client.get_collection(cfg.collection)
            # If it exists but vector params differ, leave to ops to migrate; don't auto-drop.
            _ = info
            return
        except Exception:
            pass  # treat as missing

        vectors = {"size": cfg.vector_size, "distance": cfg.distance}
        self._client.create_collection(
            collection_name=cfg.collection, vectors_config=vectors
        )

    def upsert(
        self, collection: str, points: Iterable[Tuple[str, List[float], Dict]]
    ) -> int:
        """
        Upsert a batch of (id, vector, payload) points. Returns count written.
        Payload must be JSON-serializable.
        """
        ids, vecs, payloads = [], [], []
        for pid, vec, payload in points:
            ids.append(pid)
            vecs.append(vec)
            payloads.append(payload)
        if not ids:
            return 0
        self._client.upsert(
            collection_name=collection,
            points={"ids": ids, "vectors": vecs, "payloads": payloads},
        )
        return len(ids)
