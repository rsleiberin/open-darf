"""Receipt helpers (write tiny JSON receipts under docs/audit/pipeline/...)."""

import json
import time
from pathlib import Path


def write_receipt(bucket: str, name: str, payload: dict) -> str:
    stamp = time.strftime("%Y%m%d-%H%M%S", time.gmtime())
    outdir = Path("docs/audit/pipeline") / bucket / stamp
    outdir.mkdir(parents=True, exist_ok=True)
    f = outdir / f"{name}.json"
    f.write_text(json.dumps(payload, indent=2))
    return str(f)
