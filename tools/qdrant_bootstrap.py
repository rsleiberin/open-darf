#!/usr/bin/env python3
from __future__ import annotations
import os
import json
import urllib.request
import urllib.error
import datetime
import pathlib

HOST = os.environ.get("QDRANT_HTTP", "http://127.0.0.1:6333")
COLL = os.environ.get("QDRANT_COLL", "facts")
D = int(os.environ.get("QDRANT_D", "384"))


def req(method: str, path: str, data=None):
    url = HOST + path
    body = None
    if data is not None:
        body = json.dumps(data).encode("utf-8")
    r = urllib.request.Request(url, data=body, method=method)
    if data is not None:
        r.add_header("Content-Type", "application/json")
    with urllib.request.urlopen(r, timeout=10) as resp:
        return json.loads(resp.read().decode())


def main() -> int:
    # Create if missing
    try:
        req("GET", f"/collections/{COLL}")
    except Exception:
        req(
            "PUT",
            f"/collections/{COLL}",
            {
                "vectors": {"size": D, "distance": "Cosine"},
                "hnsw_config": {"m": 16, "ef_construct": 128},
            },
        )
    # Receipt
    info = req("GET", f"/collections/{COLL}")
    stamp = datetime.datetime.utcnow().strftime("%Y%m%d-%H%M%S")
    outdir = pathlib.Path("docs/audit/storage_bootstrap") / stamp
    outdir.mkdir(parents=True, exist_ok=True)
    (outdir / "qdrant_info.json").write_text(
        json.dumps(
            {
                "timestamp_utc": datetime.datetime.utcnow().isoformat(
                    timespec="seconds"
                )
                + "Z",
                "info": info,
            },
            indent=2,
        ),
        encoding="utf-8",
    )
    print(f"Qdrant bootstrap receipt → {outdir}/qdrant_info.json")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
