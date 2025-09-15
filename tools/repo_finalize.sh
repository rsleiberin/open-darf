#!/usr/bin/env bash
set -euo pipefail
export PS4='+ ${EPOCHREALTIME} ${BASH_SOURCE}:${LINENO}: '

echo "=== [Phase 7R · Repo Finalize · merge+push+prune] ==="
ROOT="$(git rev-parse --show-toplevel 2>/dev/null || true)"
echo "[info] repo root: ${ROOT:-<not-a-git-repo>}"
if [[ -z "$ROOT" ]]; then echo "[fatal] not a git repo"; exit 2; fi
cd "$ROOT"

TS="$(date -u +%Y%m%dT%H%M%SZ)"
OUTDIR="var/receipts/${TS}_repo_finalize"
mkdir -p "$OUTDIR"
LOG="$OUTDIR/finalize.log"
exec > >(tee -a "$LOG") 2>&1
set -x

# --- Inspect remotes & default branch ----------------------------------------
git fetch --all --prune

default_ref="$(git symbolic-ref -q --short refs/remotes/origin/HEAD || true)" # e.g. origin/main
DEFAULT_BRANCH="${default_ref#origin/}"
if [[ -z "$DEFAULT_BRANCH" ]]; then
  if git show-ref --verify --quiet refs/heads/main; then DEFAULT_BRANCH="main";
  elif git show-ref --verify --quiet refs/heads/master; then DEFAULT_BRANCH="master";
  else echo "[fatal] could not determine default branch"; exit 3; fi
fi
echo "[info] default branch: ${DEFAULT_BRANCH}"

CUR_BRANCH="$(git branch --show-current)"
echo "[info] current branch: ${CUR_BRANCH}"

# Preferred feature branch if it exists; otherwise use current (if not default)
FEATURE_BRANCH=""
if git show-ref --verify --quiet refs/heads/phase7r/native-ubuntu-validator; then
  FEATURE_BRANCH="phase7r/native-ubuntu-validator"
elif [[ "$CUR_BRANCH" != "$DEFAULT_BRANCH" && -n "$CUR_BRANCH" ]]; then
  FEATURE_BRANCH="$CUR_BRANCH"
fi
echo "[info] feature branch candidate: ${FEATURE_BRANCH:-<none>} (ok if none)"

# --- Safety net for local changes --------------------------------------------
if ! git diff --quiet || ! git diff --cached --quiet; then
  STASH_NAME="pre-finalize-${TS}"
  git stash push -u -m "$STASH_NAME"
  echo "[safety] stashed local changes as: $STASH_NAME"
fi

# --- Update default branch ----------------------------------------------------
git checkout "$DEFAULT_BRANCH"
git pull --ff-only origin "$DEFAULT_BRANCH" || git pull origin "$DEFAULT_BRANCH"

# --- Merge feature branch (if any) -------------------------------------------
if [[ -n "$FEATURE_BRANCH" && "$FEATURE_BRANCH" != "$DEFAULT_BRANCH" ]]; then
  echo "[merge] merging ${FEATURE_BRANCH} -> ${DEFAULT_BRANCH}"
  git merge --no-ff "$FEATURE_BRANCH" -m "merge(phase7r): validator+receipts+WSL-gate+net_probe+CPU-fallback+report pack"
else
  echo "[merge] no feature branch to merge (skipped)"
fi

# --- Tag the state ------------------------------------------------------------
TAG="phase7r-complete-${TS}"
git tag -a "$TAG" -m "Phase 7R complete: validator, receipts, WSL gate explainer, net_probe, CPU fallback, report bundling"
echo "[tag] created: $TAG"

# --- Push to available remotes ------------------------------------------------
for R in origin open-darf darf-source; do
  if git remote get-url "$R" >/dev/null 2>&1; then
    echo "[push] pushing ${DEFAULT_BRANCH} + tags to $R"
    git push "$R" "$DEFAULT_BRANCH"
    git push "$R" --tags
  fi
done

# --- Prune merged branches (local) -------------------------------------------
echo "[prune] local merged branches -> deleting (except main/master/develop)"
while read -r br; do
  [[ -z "$br" ]] && continue
  if [[ "$br" != "$DEFAULT_BRANCH" && "$br" != "develop" && "$br" != "main" && "$br" != "master" ]]; then
    git branch -d "$br" || true
  fi
done < <(git branch --merged "$DEFAULT_BRANCH" | sed 's/^\* //;s/^  //')

# --- Prune feature branch on remotes (if present) ----------------------------
if [[ -n "$FEATURE_BRANCH" && "$FEATURE_BRANCH" != "$DEFAULT_BRANCH" ]]; then
  for R in origin open-darf darf-source; do
    if git remote get-url "$R" >/dev/null 2>&1; then
      if git ls-remote --exit-code --heads "$R" "$FEATURE_BRANCH" >/dev/null 2>&1; then
        echo "[prune] deleting remote branch $R/$FEATURE_BRANCH"
        git push "$R" --delete "$FEATURE_BRANCH" || true
      fi
    fi
  done
fi

# --- Remote prune & gc --------------------------------------------------------
for R in $(git remote); do
  git remote prune "$R" || true
done
git gc --prune=now --aggressive || true

# --- Optional working tree clean (OFF by default) ----------------------------
# Set CLEAN=1 to remove untracked/ignored files (DANGEROUS/irreversible).
if [[ "${CLEAN:-0}" == "1" ]]; then
  echo "[clean] removing untracked & ignored files (git clean -fdx)"
  git clean -fdx
else
  echo "[clean] preview (set CLEAN=1 to actually clean):"
  git clean -ndx || true
fi

# --- Summary -----------------------------------------------------------------
echo "=== Summary ==="
echo "[summary] default branch: $DEFAULT_BRANCH"
echo "[summary] feature merged: ${FEATURE_BRANCH:-<none>}"
echo "[summary] tag: $TAG"
echo "[summary] remotes: $(git remote | tr '\n' ' ')"
echo "[summary] receipt: $LOG"
echo "=== DONE ==="
