# AGENT_TLA_GUIDE.md  (compact)

This is the “ops + spec-surgery” cheat-sheet for running and repairing DARF TLA on our box.

## 0) Box profile & defaults
- CPU: Ryzen 7 5800X (8C/16T).  Workers sweet spot: 8–12.
- RAM: 16 GiB.  TLC heap: 10–12 GiB (leave headroom for OS).
- OS: WSL2 Ubuntu.  Disk is plenty (>100 GiB free recommended).

**Environment knobs (use these unless a config says otherwise):**
- Fingerprint index: `-fp 88` (keep constant across a run + recovery).
- JVM: `JAVA_TOOL_OPTIONS="-XX:+UseParallelGC -Xmx10g -XX:+ExitOnOutOfMemoryError"`
- Off-heap fingerprints (optional): `-Dtlc2.tool.fp.offheap.size=2048` (MB)
- Checkpoint: `-Dutil.checkpoint=300000` (60×5s) + unique `-metadir`.
- Limits: `ulimit -n 65535`

## 1) Start a fresh TLC run (with checkpointing)

ROOT=~/darf-source/docs/darf/spec/tla
RUNS="$ROOT/runs"
STAMP=$(date +%F-%H%M%S)
METADIR="$RUNS/states_valid_n5-$STAMP"
LOG="$RUNS/valid_n5-$STAMP.log"
mkdir -p "$METADIR"

ulimit -n 65535
WORKERS=12
FP=88
XMX=10g
FP_OFFHEAP_MB=2048

JAVA_TOOL_OPTIONS="-XX:+UseParallelGC -Xmx$XMX -XX:+ExitOnOutOfMemoryError"
java -Dtlc2.tool.fp.offheap.size=$FP_OFFHEAP_MB
-Dutil.checkpoint=300000
-jar ~/darf-source/tools/tla2tools.jar
-fp $FP
-workers $WORKERS
-config "$ROOT/models/Model_valid_n5.cfg"
"$ROOT/models/Model_valid_n5.tla"
-metadir "$METADIR" | tee "$LOG"

**Live view + naive ETA (optimistic):**

stdbuf -oL tail -f "$LOG" | grep -E 'Progress|Checking temporal|left on queue'
awk '/Progress/{ gen=$0; sub(/.generated (/,"",gen); sub(/ s/min./,"",gen);
q=$0; sub(/.,\s/,"",q); sub(/ states left on queue./,"",q);
if(gen+0>0){eta=q/gen60; printf "Queue=%s, Gen/min=%s => ~%.1f min\n",q,gen,eta/60 }}' "$LOG"

stdbuf -oL tail -f "$LOG" | grep -E 'Progress|Checking temporal|left on queue'
awk '/Progress/{ gen=$0; sub(/.generated (/,"",gen); sub(/ s/min./,"",gen);
q=$0; sub(/.,\s/,"",q); sub(/ states left on queue./,"",q);
if(gen+0>0){eta=q/gen60; printf "Queue=%s, Gen/min=%s => ~%.1f min\n",q,gen,eta/60 }}' "$LOG"

## 2) Recovery (resume from a checkpoint)
- Pick the **same** `-fp` and **same worker count** as the checkpoint.
- If liveness files are corrupt, wipe only the liveness folder under the metadir.

ROOT=~/darf-source/docs/darf/spec/tla
METADIR=$(ls -1dt "$ROOT/runs"/states_valid_n5-* | head -1)
RECOVER_DIR=$(ls -1dt "$METADIR"/* | head -1)
ls "$RECOVER_DIR"/vars.chkpt >/dev/null || { echo "No complete checkpoint"; exit 1; }

WORKERS=$(ls -1 "$RECOVER_DIR"/Model_valid_n5-*.chkpt | wc -l)
FP=88
XMX=12g

If previous run crashed during liveness phase:
find "$METADIR" -maxdepth 2 -type d -name liveness -print -exec rm -rf {} +

JAVA_TOOL_OPTIONS="-XX:+UseParallelGC -Xmx$XMX -XX:+ExitOnOutOfMemoryError"
java -jar ~/darf-source/tools/tla2tools.jar
-fp $FP
-workers $WORKERS
-recover "$RECOVER_DIR"
-config "$ROOT/models/Model_valid_n5.cfg"
"$ROOT/models/Model_valid_n5.tla"
-metadir "$METADIR"


## 3) Spec-surgery patterns that kept biting us

### A) “Unknown operator” caused by mis-typed disjunct
Symptom: `Unknown operator: NextRound` while `NextRound ==` exists.
Cause: a stray line like `/ NextRound` (missing backslash).

**Fix:** ensure the **top-level** Next has the disjunct *exactly* `\/ NextRound`
and there’s only one such disjunct inside `Next == ...`.

Quick check:

awk '/^Next[[:space:]]==/{f=1} f{print} /^[[:space:]]$/{if(f)exit}' DARFProcessConformance.tla
grep -n '^[[:space:]]*\/[[:space:]]NextRound[[:space:]]$' DARFProcessConformance.tla
grep -n '^[[:space:]]NextRound[[:space:]]==' DARFProcessConformance.tla

awk '/^Next[[:space:]]==/{f=1} f{print} /^[[:space:]]$/{if(f)exit}' DARFProcessConformance.tla
grep -n '^[[:space:]]*\/[[:space:]]NextRound[[:space:]]$' DARFProcessConformance.tla
grep -n '^[[:space:]]NextRound[[:space:]]==' DARFProcessConformance.tla

sed -i -E 's|^[[:space:]]*/[[:space:]]NextRound[[:space:]]$| \/ NextRound|' DARFProcessConformance.tla


### C) Preference uniqueness guard
Intent: each honest p contributes at most one preference (any value).
**Guard to use:**

/\ ~( \E x \in {"A","B","C"} : <<p, x>> \in Preferences )

Use this inside `CollectPreference(p, pref)` instead of testing a single tuple.

### D) StartAggregation should clear volatile sets (but not Decisions/Round)
We want to move to Aggregate with a clean voting context:

StartAggregation ==
/\ Phase = "Agree"
/\ \A q \in ActiveQuorums : \A p \in q \ Faulty :
\E value \in {"A","B","C"} : <<p, value>> \in Decisions
/\ Phase' = "Aggregate"
/\ ActiveQuorums' = {}
/\ Votes' = {}
/\ UNCHANGED <<Preferences, Decisions, Round>>

### E) AggregateResults resets for next epoch (incl. Decisions)
To avoid ProcessConformance false positives across epochs, reset:

AggregateResults ==
/\ Phase = "Aggregate"
/\ Phase' = "Collect"
/\ Round' = Round + 1
/\ Preferences' = {}
/\ ActiveQuorums' = {}
/\ Votes' = {}
/\ Decisions' = {}

Ensure `Next` contains `\/ AggregateResults`.

## 4) Frequent errors → fast fixes

- **`Unknown operator: NextRound`**
  - Verify only one `NextRound ==` (not commented) and one `\/ NextRound` in `Next`.
  - Fix stray `/ NextRound`.

- **`Couldn't resolve infix operator '/'`**
  - Same root cause as above. Replace bare `/` with `\/`.

- **`java.io.EOFException` in liveness**
  - The liveness disk graph is corrupt. Delete `*/liveness/` under the metadir,
    then rerun recovery with the same `-fp` & `-workers`.

- **`java.lang.OutOfMemoryError: Java heap space`**
  - Resume with higher `-Xmx` (e.g., 12g) OR split into smaller runs.
  - If GC thrashes: lower workers by 2, or reduce state with VIEW/model-values.

- **`FileNotFound vars.chkpt` on recover**
  - Checkpoint incomplete. Pick an older checkpoint directory that *has* `vars.chkpt`.

- **Worker mismatch on recover**
  - Count `Model_valid_n5-*.chkpt`, set `-workers` to that count.

## 5) Performance & stability on this box

- Workers: 10–12 usually best; if RAM pressure appears, drop to 8–10.
- Heap: start 10 GiB; for recovery or long liveness, use 12 GiB.
- Checkpointing: always on; unique `-metadir` per run; don’t reuse.
- Throughput target: multi-million states/min is normal once warmed up.
- When you change the spec materially, **start a new run** (don’t recover).

## 6) Minimal health checks (before long runs)

- `Spec == Init /\ [][Next]_vars` exists.
- `ProcessConformance` included in `SafetyInvariant` or model checks it.
- `Next` contains exactly one of each disjunct we expect.
- No commented headers shadowing real ones (grep for `^.*==` and check).

## 7) Small-model first (policy)
- Strip liveness for first proof passes (safety only).
- Use model values + tight bounds; add symmetry only when no liveness.
- Grow parameters along a ladder; accept the smallest config that exercises the property.

## 8) Micro-playbook

**Fresh run**
1. Bump ulimit; set XMX, fp, workers; unique metadir.
2. Kick off; watch progress lines; compute naive ETA; if ETA > 8h, reconsider (shrink or shard).

**On OOM**
1. Stop; recover with larger heap OR fewer workers.
2. If recurring, consider VIEW / bounds or split configs.

**On liveness EOF**
1. Delete liveness dir under metadir.
2. Recover with same `-fp` and workers.

**On “unknown operator”**
1. Inspect `Next ==` block; fix bad `\/` line; re-parse (`java -jar …` should pass semantic phase).

## 9) Status line (for continuity)
- We have stable patterns for: NextRound inclusion, CollectPreference uniqueness,
  StartAggregation cleanup, AggregateResults epoch reset.
- Recovery is reliable if `vars.chkpt` exists and liveness is cleaned when corrupt.
- Use this guide to keep runs reproducible and avoid the known foot-guns.

# Background verification is running detached.

- Session: tmux `tlc_verify`
- Safety run dir: latest `runs/states_valid_n5-safety-*/`
- Liveness run dir: will appear as `runs/states_valid_n5-live-*/` after safety completes
- Logs: `run.log` inside each run dir
- Status: `scripts/tlc_status.sh` prints session state + recent progress lines
- Ticket: see `runs/_tickets/tlc-verify-<timestamp>.yml` for parameters


(End of file)
