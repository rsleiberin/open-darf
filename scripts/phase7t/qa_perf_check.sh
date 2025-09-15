#!/usr/bin/env bash
set -euo pipefail
TARGET="${1:-docs/phase7s}"
TS="$(date -u +'%Y%m%dT%H%M%SZ')"
OUTDIR="var/reports/phase7t"
AUDIT="docs/audit/phase7t"
MANIFEST="$OUTDIR/manifest_${TS}.json"

# time hashing
START_NS=$(date +%s%N)
scripts/phase7t/hash_and_manifest.py "$TARGET" --out "$MANIFEST" >/dev/null
MID_NS=$(date +%s%N)

# verify schema (quiet)
if command -v jq >/dev/null 2>&1; then
  scripts/phase7t/verify_provenance.sh "$MANIFEST" >/dev/null
else
  python3 - "$MANIFEST" >/dev/null <<'PY'
import json,sys
j=json.load(open(sys.argv[1]))
assert j.get("schema_version")==1
assert isinstance(j.get("entries"),list)
assert isinstance(j.get("manifest_sha256"),str)
PY
fi
END_NS=$(date +%s%N)

# metrics
ELAPSE_HASH_MS=$(( (MID_NS - START_NS)/1000000 ))
ELAPSE_VERIFY_MS=$(( (END_NS - MID_NS)/1000000 ))
ELAPSE_TOTAL_MS=$(( (END_NS - START_NS)/1000000 ))

ENTRIES=$(python3 - <<'PY' "$MANIFEST"
import json,sys
print(len(json.load(open(sys.argv[1])).get("entries",[])))
PY
)

# receipt
REC="$AUDIT/qa_perf_${TS}.json"
python3 - <<'PY' "$REC" "$MANIFEST" "$ELAPSE_HASH_MS" "$ELAPSE_VERIFY_MS" "$ELAPSE_TOTAL_MS" "$ENTRIES"
import json,sys,platform,os
rec,man,eh,ev,et,en = sys.argv[1:]
j={
  "schema_version":1,
  "phase":"7T",
  "action":"qa_perf_verify",
  "timestamp_utc":man.split("manifest_")[-1].split(".json")[0],
  "host":{"system":platform.system(),"kernel":platform.release(),"machine":platform.machine()},
  "links":[{"rel":"manifest","path":man}],
  "status":"ok",
  "details":{
    "entries":int(en),
    "elapsed_ms":{"hash":int(eh),"verify":int(ev),"total":int(et)}
  }
}
json.dump(j,open(rec,"w"),indent=2,sort_keys=True)
print(rec)
PY
