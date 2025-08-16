import json, os, time, pytest
from pathlib import Path

# Prefer the new function; fallback to old name if present
try:
    from apps.transform.pipeline import validate_neo4j as validate
except Exception:
    from apps.transform.pipeline import validate

try:
    from apps.validator.neo4j_client import ValidatorClient
    HAVE_DRIVER = True
except Exception:
    HAVE_DRIVER = False

from apps.transform.pipeline import ingest

pytestmark = pytest.mark.skipif(
    not (os.getenv("NEO4J_URL") and os.getenv("QDRANT_URL") and os.getenv("MINIO_ENDPOINT")),
    reason="NEO4J_URL/QDRANT_URL/MINIO_ENDPOINT not set"
)

def test_ingest_validate_end_to_end(tmp_path):
    if not HAVE_DRIVER:
        pytest.skip("neo4j python driver not available")
    vc = ValidatorClient()
    try:
        try:
            if not vc.ping():
                pytest.skip("Neo4j not reachable")
        except Exception:
            pytest.skip("Neo4j not reachable")
    finally:
        vc.close()

    sample = tmp_path/"sample.txt"
    sample.write_text("neo4j validation path")
    draft_path = ingest(str(sample), user_id="ryan")
    t0 = time.perf_counter()
    out_path = validate(str(draft_path))
    ms = (time.perf_counter()-t0)*1000

    d = json.loads(Path(out_path).read_text())
    assert d["status"]=="ready_for_review"
    assert d["validation"]["status"]=="pass"
    assert d["validation"]["latency_ms"] >= 0
    assert ms < 500
