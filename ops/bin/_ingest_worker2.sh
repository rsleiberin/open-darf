#!/usr/bin/env bash
set -euo pipefail

ROOT="$1"; F="$2"
CAS_IDX="$ROOT/var/cache/cas.exists"
META_IDX="$ROOT/var/cache/file.meta"
LOCK_APP="$ROOT/ops/bin/_flock_append.sh"

mkdir -p "$ROOT/var/cache"

# Gather file metadata
if ! [[ -f "$F" ]]; then
  printf '{"path":"%s","error":"missing"}\n' "$F"
  exit 0
fi
SIZE="$(stat -c %s "$F")"
MTIM="$(stat -c %Y "$F")"

DIGEST=""

# Optional fast path: reuse digest if size+mtime unchanged
if [[ "${ALLOW_MTIME_SIZE_CACHE:-1}" = "1" ]] && [[ -s "$META_IDX" ]]; then
  # Format: path|size|mtime|digest  (match by size|mtime)
  # tail -n1 in case of duplicates; last seen is most relevant
  LINE="$(grep -F "|$SIZE|$MTIM|" "$META_IDX" 2>/dev/null | tail -n1 || true)"
  if [[ -n "$LINE" ]]; then
    DIGEST="${LINE##*|}"
  fi
fi

# If digest unknown, hash now
if [[ -z "$DIGEST" ]]; then
  # sha256sum outputs: "<digest>  <path>"
  DIGEST="$(sha256sum "$F" | awk '{print $1}')"
fi

# Determine existence
HAVE_REMOTE=0
if [[ -s "$CAS_IDX" ]] && grep -Fxq "$DIGEST" "$CAS_IDX" 2>/dev/null; then
  HAVE_REMOTE=1
else
  # Try helper scripts in order of preference
  if [[ -x "$ROOT/ops/bin/cas_have.sh" ]]; then
    if "$ROOT/ops/bin/cas_have.sh" "$DIGEST" >/dev/null 2>&1; then HAVE_REMOTE=1; fi
  elif [[ -x "$ROOT/ops/bin/mc_host.sh" ]]; then
    # mc_host abstracts auth/alias; stat returns non-zero if not found
    if "$ROOT/ops/bin/mc_host.sh" stat "local/cas/$DIGEST" >/dev/null 2>&1; then HAVE_REMOTE=1; fi
  else
    # Last resort: try within the minio container if mc is available
    if docker ps --format '{{.Names}}' | grep -q '^darf-minio-1$'; then
      if docker exec -i darf-minio-1 mc stat --json local/cas/"$DIGEST" >/dev/null 2>&1; then HAVE_REMOTE=1; fi
    fi
  fi
fi

# Upload if missing
if (( HAVE_REMOTE == 0 )); then
  if [[ -x "$ROOT/ops/bin/cas_put.sh" ]]; then
    "$ROOT/ops/bin/cas_put.sh" "$F" "$DIGEST" >/dev/null 2>&1 || true
  elif [[ -x "$ROOT/ops/bin/mc_host.sh" ]]; then
    "$ROOT/ops/bin/mc_host.sh" cp "$F" "local/cas/$DIGEST" >/dev/null 2>&1 || true
  else
    # Worst-case fallback (may be slower)
    if docker ps --format '{{.Names}}' | grep -q '^darf-minio-1$'; then
      # If /host is not mounted in container, this may fail; we don't hard-fail the pipeline.
      docker exec -i darf-minio-1 mc cp -q /host"$F" local/cas/"$DIGEST" >/dev/null 2>&1 || true
    fi
  fi
  HAVE_REMOTE=1
fi

# Update local indexes with locks (idempotent lines ok)
"$LOCK_APP" "$CAS_IDX"  "$DIGEST"
"$LOCK_APP" "$META_IDX" "$F|$SIZE|$MTIM|$DIGEST"

# Emit a JSONL record
# Use POSIX path; best-effort realpath
if command -v realpath >/dev/null 2>&1; then
  PTH="$(realpath -s "$F" 2>/dev/null || echo "$F")"
else
  PTH="$F"
fi
printf '{"path":"%s","digest":"%s","size":%s,"mtime":%s}\n' "$PTH" "$DIGEST" "$SIZE" "$MTIM"
