#!/usr/bin/env python3
from __future__ import annotations
import os
import json
import sys
import base64
import datetime
import pathlib
import urllib.request

USER = os.environ.get("NEO4J_USER", "neo4j")
PWD = os.environ.get("NEO4J_PASSWORD", "neo4jpass")
AUTH = base64.b64encode(f"{USER}:{PWD}".encode()).decode()
HDR = {"Authorization": f"Basic {AUTH}", "Content-Type": "application/json"}
URL = os.environ.get("NEO4J_TX_URL", "http://127.0.0.1:7474/db/neo4j/tx/commit")


def post(stmt: str):
    req = urllib.request.Request(
        URL,
        data=json.dumps({"statements": [{"statement": stmt}]}).encode(),
        headers=HDR,
        method="POST",
    )
    with urllib.request.urlopen(req, timeout=10) as r:
        return json.loads(r.read().decode())


def main(path: str) -> int:
    text = pathlib.Path(path).read_text(encoding="utf-8")
    stmts = [s.strip() for s in text.split(";") if s.strip()]
    results = []
    for s in stmts:
        results.append(post(s))
    stamp = datetime.datetime.utcnow().strftime("%Y%m%d-%H%M%S")
    outdir = pathlib.Path("docs/audit/storage_bootstrap") / stamp
    outdir.mkdir(parents=True, exist_ok=True)
    (outdir / "neo4j_apply.json").write_text(
        json.dumps(
            {
                "timestamp_utc": datetime.datetime.utcnow().isoformat(
                    timespec="seconds"
                )
                + "Z",
                "results": results,
            },
            indent=2,
        ),
        encoding="utf-8",
    )
    print(f"Neo4j bootstrap receipt → {outdir}/neo4j_apply.json")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1] if len(sys.argv) > 1 else "tools/neo4j_bootstrap.cql"))
