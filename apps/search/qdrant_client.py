from __future__ import annotations
import os
from typing import Any, Dict, List, Optional

from qdrant_client import QdrantClient
from qdrant_client.models import (
    Distance,
    VectorParams,
    PointStruct,
    Filter,
    FieldCondition,
    MatchValue,
)


class QdrantSearch:
    def __init__(
        self, url: Optional[str] = None, collection: Optional[str] = None
    ) -> None:
        self.url = url or os.getenv("QDRANT_URL", "http://localhost:6333")
        self.collection = collection or os.getenv("QDRANT_COLLECTION", "anchors")
        self.client = QdrantClient(url=self.url)

    def ensure_collection(self, dim: int, distance: str = "Cosine") -> None:
        # Create if missing; don't drop existing data if present
        try:
            self.client.get_collection(self.collection)
            return
        except Exception:
            pass
        self.client.create_collection(
            collection_name=self.collection,
            vectors_config=VectorParams(
                size=dim, distance=getattr(Distance, distance.upper())
            ),
        )

    def upsert(
        self,
        vector: List[float],
        payload: Dict[str, Any],
        point_id: Optional[int] = None,
    ) -> int:
        pid = point_id if point_id is not None else payload.get("id")
        if pid is None:
            # simple deterministic id if not provided
            pid = abs(hash((tuple(vector), frozenset(payload.items())))) % (2**31)
        self.client.upsert(
            collection_name=self.collection,
            points=[PointStruct(id=pid, vector=vector, payload=payload)],
        )
        return pid

    def query(self, vector: List[float], top_k: int = 5, user_id: Optional[str] = None):
        qf = None
        if user_id:
            qf = Filter(
                must=[FieldCondition(key="user_id", match=MatchValue(value=user_id))]
            )
        return self.client.search(
            collection_name=self.collection,
            query_vector=vector,
            with_payload=True,
            limit=top_k,
            query_filter=qf,
        )

    def delete_by_anchor(self, anchor_id: str) -> None:
        f = Filter(
            must=[FieldCondition(key="anchor_id", match=MatchValue(value=anchor_id))]
        )
        self.client.delete(collection_name=self.collection, points_selector=f)
