#!/usr/bin/env sh
# PURE wrapper — POSIX sh. Calls container entrypoint that handles deps & model.
set -eu
DATA_PATH=""; SPLIT=""; OUTDIR=""
while [ $# -gt 0 ]; do
  case "$1" in
    --data|--dataset) DATA_PATH="$2"; shift 2 ;;
    --split) SPLIT="$2"; shift 2 ;;
    --outdir) OUTDIR="$2"; shift 2 ;;
    --) shift; break ;;
    *) shift ;;
  esac
done

OUTDIR="${OUTDIR:-${PWD}/out}"
mkdir -p "${OUTDIR}"

DS_ROOT="${HOME}/darf-source"
SCIERC_DATA="${DATA_PATH:-${DS_ROOT}/data/scierc}"
IMAGE="darf/pure:py37-bullseye"

# Pull image if missing
if ! command -v docker >/dev/null 2>&1; then
  echo "[PURE] ERROR: docker not available." >&2; exit 9
fi
docker image inspect "${IMAGE}" >/dev/null 2>&1 || docker pull "${IMAGE}"

# Run entrypoint; pass SPLIT via env; stream logs
SPLIT="${SPLIT:-test}"
echo "[PURE] Using image ${IMAGE} (SPLIT=${SPLIT})"
docker run --rm \
  -e SPLIT="${SPLIT}" \
  -v "${SCIERC_DATA}:/data:ro" \
  -v "${OUTDIR}:/out" \
  "${IMAGE}" /usr/local/bin/docker_run_scierc.sh /data /out

# If container produced normalized preds.jsonl, we are done
if [ -s "${OUTDIR}/preds.jsonl" ]; then
  echo "[PURE] preds.jsonl ready at ${OUTDIR}"
  exit 0
fi

# Fallback: convert predictions.json if present
if [ -s "${OUTDIR}/predictions.json" ]; then
  python3 - "${OUTDIR}/preds.jsonl" "${OUTDIR}/predictions.json" << 'PY'
import json, sys
dst, src = sys.argv[1], sys.argv[2]
with open(src) as f: data = json.load(f)
with open(dst, "w") as w:
    if isinstance(data, list):
        for r in data: w.write(json.dumps(r)+"\n")
    elif isinstance(data, dict):
        for k,v in data.items(): w.write(json.dumps({k:v})+"\n")
    else:
        w.write(json.dumps({"pred": data})+"\n")
print("[PURE] Wrote", dst)
PY
  exit 0
fi

echo "[PURE] ERROR: No predictions produced." >&2
exit 1
