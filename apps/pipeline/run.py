from typing import Iterable, Tuple, Dict, Any
from apps.pipeline.parse import extract_text
from apps.pipeline.process import run_bias_checks
from apps.pipeline.receipts import write_receipt


def run_once(source, bucket: str = "e2e") -> Tuple[int, str]:
    """
    Pull all refs from `source` (must support .list() & .fetch()),
    parse and process each, and write a small receipt.
    Returns (count_processed, receipt_path).
    """
    refs: Iterable[str] = list(source.list())
    reports: Dict[str, Any] = {}
    for ref in refs:
        text, hint = extract_text(source.fetch(ref), "text/plain")
        reports[ref] = {"parser": hint, "bias": run_bias_checks(text)}
    path = write_receipt(bucket, "run_once", {"count": len(refs), "reports": reports})
    return len(refs), path
