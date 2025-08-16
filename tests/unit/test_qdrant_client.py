import os, pytest
from apps.search.qdrant_client import QdrantSearch

pytestmark = pytest.mark.skipif(not os.getenv("QDRANT_URL"), reason="QDRANT_URL not set; source .env.local or run bin/use-env.sh")

def test_upsert_and_search_top1_and_filter():
    q = QdrantSearch()
    q.ensure_collection(dim=3, distance="Cosine")

    # Clean slate: use a unique collection for unit tests to avoid collisions
    # (Alternatively, run recreate_collection, but we keep it non-destructive for now.)
    # Insert three one-hot points
    q.upsert([1,0,0], {"anchor_id":"a1","user_id":"ryan"}, point_id=1)
    q.upsert([0,1,0], {"anchor_id":"a2","user_id":"ryan"}, point_id=2)
    q.upsert([0,0,1], {"anchor_id":"a3","user_id":"ryan"}, point_id=3)

    # Top1 should be id=1 for [1,0,0]
    res = q.query([1,0,0], top_k=3)
    assert res[0].id == 1

    # Filter by user_id (same result here, but verifies filter path)
    resf = q.query([1,0,0], top_k=3, user_id="ryan")
    assert resf[0].id == 1
