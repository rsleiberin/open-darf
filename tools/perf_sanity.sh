#!/usr/bin/env bash
set -Eeuo pipefail
cd "$(dirname "$0")/.."

stamp="$(date -u +%Y%m%d-%H%M%S)"
out="docs/audit/perf_sanity/$stamp"; mkdir -p "$out"

python3 - "$out" <<'PY'
import sys, os, json, time, statistics, datetime
from apps.hyperrag.extract import RegexEntityExtractor
from apps.hyperrag.guard import evaluate_action

outdir = sys.argv[1]
text=("Alice met ACME Corporation in Austin with Bob from Beta Labs. "
      "Charlie joined from New York; Delta Systems dialed in.")*30

# extractor bench
E=RegexEntityExtractor()
lat=[];
for _ in range(300):
    t=time.perf_counter(); E.extract(text); lat.append((time.perf_counter()-t)*1000)
lat.sort()
ext = {"p50_ms": round(statistics.median(lat),3), "p95_ms": round(lat[int(0.95*len(lat))-1],3)}

# guard bench
lat=[];
for _ in range(10000):
    t=time.perf_counter(); evaluate_action("graph.upsert_entity", {"etype":"Concept"}); lat.append((time.perf_counter()-t)*1000)
lat.sort()
grd = {"p50_ms": round(statistics.median(lat),4), "p95_ms": round(lat[int(0.95*len(lat))-1],4)}

data={"timestamp_utc": datetime.datetime.utcnow().isoformat(timespec="seconds")+"Z", "extractor": ext, "guard": grd}
os.makedirs(outdir, exist_ok=True)
json.dump(data, open(os.path.join(outdir,"summary.json"),"w"), indent=2)
print(f"perf sanity → {outdir}/summary.json  extractor.p95={ext['p95_ms']}ms  guard.p95={grd['p95_ms']}ms")
PY
