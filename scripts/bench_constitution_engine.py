import json
import os
import time
from pathlib import Path
from statistics import quantiles
from typing import Dict, Any

from apps.constitution_engine.config import load_config
from apps.constitution_engine.engine import ConstraintEngine

TARGET_MS = float(os.getenv("CCE_TARGET_MS", "170.0"))


def p95(vals):
    # statistics.quantiles with n=20 -> 95th approx
    return quantiles(vals, n=20)[18]


def bench(n: int = 400) -> Dict[str, Any]:
    cfg = load_config()
    engine = ConstraintEngine(cfg.uri, cfg.user, cfg.password)
    try:
        lat = []
        for i in range(n):
            op = {"principal": "u:demo", "action": "read", "resource": f"doc:{i%10}"}
            res = engine.validate(op)
            lat.append(res.elapsed_ms)
        return {
            "result": "ok",
            "n": n,
            "p50_ms": sorted(lat)[len(lat) // 2],
            "p95_ms": p95(lat),
            "max_ms": max(lat),
            "avg_ms": sum(lat) / len(lat),
            "target_ms": TARGET_MS,
            "neo4j_enabled": bool(cfg.uri and cfg.user and cfg.password),
        }
    finally:
        engine.close()


def main():
    out = bench()
    ts = time.strftime("%Y%m%d-%H%M%S", time.gmtime())
    dirp = Path("docs/audit/stream1") / ts
    dirp.mkdir(parents=True, exist_ok=True)
    with (dirp / "validation.json").open("w") as f:
        json.dump(out, f, indent=2)
    print(dirp)


if __name__ == "__main__":
    main()
