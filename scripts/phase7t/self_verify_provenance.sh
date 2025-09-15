#!/usr/bin/env bash
set -euo pipefail

TARGETS=("${@:-docs/phase7s}")
TS="$(date -u +'%Y%m%dT%H%M%SZ')"

OUTDIR="var/reports/phase7t"
AUDIT="docs/audit/phase7t"
MANIFEST="$OUTDIR/manifest_${TS}.json"

echo "[hash] -> $MANIFEST"
scripts/phase7t/hash_and_manifest.py "${TARGETS[@]}" --out "$MANIFEST"

echo "[verify] schema"
if command -v jq >/dev/null 2>&1; then
  scripts/phase7t/verify_provenance.sh "$MANIFEST"
else
  python3 - <<'PY' "$MANIFEST"
import json,sys
j=json.load(open(sys.argv[1]))
assert j.get("schema_version")==1
assert isinstance(j.get("entries"),list)
assert isinstance(j.get("manifest_sha256"),str)
print("[ok] minimal schema checks passed")
PY
fi

# Anchor receipt
ANCHOR="$AUDIT/anchor_manifest_${TS}.json"
python3 - <<'PY' "$MANIFEST" "$ANCHOR"
import json,sys,platform,time
m=sys.argv[1]; r=sys.argv[2]
j=json.load(open(m))
rec={
  "schema_version":1,
  "phase":"7T",
  "action":"anchor_manifest",
  "timestamp_utc":time.strftime("%Y%m%dT%H%M%SZ", time.gmtime()),
  "host":{"system":platform.system(),"kernel":platform.release(),"machine":platform.machine()},
  "provenance":{
    "algorithm":"sha256",
    "canonicalization":"utf8+lf+trim-trailing",
    "manifest_path":m,
    "manifest_sha256":j.get("manifest_sha256","")
  },
  "links":[{"rel":"manifest","path":m}],
  "status":"ok",
  "details":{"entries":len(j.get("entries",[]))}
}
json.dump(rec,open(r,"w"),indent=2,sort_keys=True)
print(f"[ok] wrote {r}")
PY

# Local CAS store with dedup metrics
CASREC="$AUDIT/cas_local_${TS}.json"
scripts/phase7t/cas_local.py "$MANIFEST" ".cas/sha256" "$CASREC"

echo "=== Summary ==="
echo "[manifest] $MANIFEST"
echo "[receipts] $ANCHOR ; $CASREC"
