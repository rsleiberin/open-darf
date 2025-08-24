import time
from apps.document_processor import bias

SAMPLE = "We present results but offer no methodology. Clearly this is the best outcome. [1] doi:10.1/abc"


def test_latency_under_2s():
    t0 = time.perf_counter()
    _ = bias.classify_text(SAMPLE, threshold=0.4, emit_receipt=True)
    elapsed_ms = (time.perf_counter() - t0) * 1000.0
    assert elapsed_ms < 2000.0
