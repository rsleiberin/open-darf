from typing import Iterable, Tuple, Dict, Any
import os
import time
import statistics
from apps.pipeline.parse import extract_text
from apps.pipeline.process import run_bias_checks
from apps.pipeline.receipts import write_receipt


def _percentile(data, p):
    if not data:
        return 0.0
    s = sorted(float(x) for x in data)
    k = (len(s) - 1) * (p / 100.0)
    f, c = int(k), min(int(k) + 1, len(s) - 1)
    if f == c:
        return s[int(k)]
    return s[f] + (s[c] - s[f]) * (k - f)


def run_once(source, bucket: str = "e2e") -> Tuple[int, str]:
    """
    Pull all refs from `source` (must support .list() & .fetch()),
    parse and process each, and write a receipt.
    If PIPELINE_PERF is truthy, include timing stats & parser counters.
    Returns (count_processed, receipt_path).
    """
    refs: Iterable[str] = list(source.list())
    want_perf = str(os.getenv("PIPELINE_PERF", "")).strip().lower() in {
        "1",
        "true",
        "yes",
        "on",
    }
    reports: Dict[str, Any] = {}
    parser_counts: Dict[str, int] = {}
    t_parse, t_process = [], []

    for ref in refs:
        b = source.fetch(ref)

        t0 = time.perf_counter()
        text, hint = extract_text(b, "text/plain")
        t1 = time.perf_counter()
        rpt = run_bias_checks(text)
        t2 = time.perf_counter()

        reports[ref] = {"parser": hint, "bias": rpt}
        parser_counts[hint] = parser_counts.get(hint, 0) + 1
        if want_perf:
            t_parse.append((t1 - t0) * 1000.0)
            t_process.append((t2 - t1) * 1000.0)

    payload: Dict[str, Any] = {"count": len(refs), "reports": reports}
    if want_perf:
        payload["perf"] = {
            "parse_ms": {
                "p50": _percentile(t_parse, 50),
                "p95": _percentile(t_parse, 95),
                "max": max(t_parse) if t_parse else 0.0,
                "avg": statistics.fmean(t_parse) if t_parse else 0.0,
                "n": len(t_parse),
            },
            "process_ms": {
                "p50": _percentile(t_process, 50),
                "p95": _percentile(t_process, 95),
                "max": max(t_process) if t_process else 0.0,
                "avg": statistics.fmean(t_process) if t_process else 0.0,
                "n": len(t_process),
            },
        }
        payload["obs"] = {"parser_counts": parser_counts}

    path = write_receipt(bucket, "run_once", payload)
    return len(refs), path
