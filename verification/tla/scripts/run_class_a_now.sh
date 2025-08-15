#!/usr/bin/env bash
set -Eeuo pipefail
ulimit -n 65535

: "${JAVA_TOOL_OPTIONS:=-XX:+UseParallelGC -Xmx4g -XX:+ExitOnOutOfMemoryError}"
export JAVA_TOOL_OPTIONS
JAR="${TLC_JAR:-$HOME/darf-source/tools/tla2tools.jar}"
ROOT="${ROOT:-$HOME/darf-source/verification/tla}"

cd "$ROOT"

run() {
  local name="$1" cfg="$2" tla="$3"
  if [[ ! -f "$cfg" ]]; then echo "[SKIP] $name (missing cfg: $cfg)"; return 0; fi
  if [[ ! -f "$tla" ]]; then echo "[SKIP] $name (missing tla: $tla)"; return 0; fi
  local fam="runs/classA-${name}-$(date +%F-%H%M%S)"
  mkdir -p "$fam"
  echo "[RUN] $name  -> $fam"
  java -jar "$JAR" -workers 4 -fp 79 \
    -config "$cfg" "$tla" \
    -metadir "$fam" | tee "$fam/tlc.log"
}

# Official Class-A set (bounded, non-vacuous)
run CA_ConstCompliance        models/classA_new/CA_ConstCompliance_A.cfg        classA_specs/CA_ConstCompliance.tla
run CA_BFT_QuorumEnum         models/classA_new/CA_BFT_QuorumEnum_A.cfg         classA_specs/CA_BFT_QuorumEnum.tla
run CA_ExplicitAuthorization  models/classA_new/CA_ExplicitAuthorization_A.cfg  classA_specs/CA_ExplicitAuthorization.tla
run CA_JoinAtMostOnce         models/classA_new/CA_JoinAtMostOnce_A.cfg         classA_specs/CA_JoinAtMostOnce.tla
run CA_IdentityPersistence    models/classA_new/CA_IdentityPersistence_A.cfg    classA_specs/CA_IdentityPersistence.tla
run CA_CapabilityEnhancement  models/classA_new/CA_CapabilityEnhancement_A.cfg  classA_specs/CA_CapabilityEnhancement.tla
run CA_RevocationAuthority    models/classA_new/CA_RevocationAuthority_A.cfg    classA_specs/CA_RevocationAuthority.tla

echo "=== Class A summary ==="
shopt -s nullglob
for log in runs/classA-*/tlc.log; do
  fam="$(basename "$(dirname "$log")")"
  if   grep -qE "Invariant .* violated" "$log"; then status="FAIL"
  elif grep -q "^Error:" "$log"; then status="ERROR"
  else status="PASS"; fi
  ds="$(grep -Eo '[0-9]+ distinct states found' "$log" | tail -1 | awk '{print $1}')"
  ds="${ds:-0}"
  echo "$fam: $status (distinct=$ds)"
done | sort
