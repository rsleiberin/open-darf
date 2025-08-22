# Class-A Verification Handoff

- Repo: /home/tank/darf-source
- Branch: feat/policy-gates-ownership-20250820-160552
- Commit: b63027c
- Timestamp (UTC): 20250821T021041Z

## What’s included
- **spec/**: `ConstitutionCore.tla`, `CC_A_cc.tla`
- **cfg/**: `CC_A_cc.quick.cfg` (wrapper-level `StateConstr`), plus main cfg if present
- **logs/**: latest SANY and quick TLC logs

## Status (quick smoke)
This run used the wrapper-level constraint `StateConstr` and completed quickly.
Inspect **logs/tlc_*.quick.out** for the verdict lines (e.g., “No error has been found”).
If you remove `StateConstr`, the state space is very large and may require managed resources.

## Repro (from repo root)
```bash
export TLA_JAR="${TLA_JAR:-/home/tank/tla/tla2tools.jar}"
cd verification/tla
java -cp "/home/tank/.local/share/tla/tla2tools.jar" tla2sany.SANY ConstitutionCore.tla
java -cp "/home/tank/.local/share/tla/tla2tools.jar" tla2sany.SANY CC_A_cc.tla
java -Xmx2G -cp "/home/tank/.local/share/tla/tla2tools.jar" tlc2.TLC -nowarning -workers 2   -config classA_cfgs/CC_A_cc.quick.cfg CC_A_cc.tla
```

## Notes for the Architect
- We aligned **CreateOperation** authorization with wrapper Owner mapping and guard insertion into `operations` by status. This cleared the quick run. Earlier unconstrained runs showed rapid state explosion.
- **Modify/Delete** operators should be reviewed to mirror the create-guard pattern if that matches your intent.
- Wrapper defines `Owner == [n \in Nodes |-> IF n = n1 THEN p1 ELSE p2]` and `MaxOperations == 5`.
- Quick constraint lives **inside the wrapper module** as `StateConstr`. The quick cfg references it by name.

## Known risks / follow-ups
- Full (unconstrained) TLC likely exceeds local resources. Recommend managed TLC for exhaustive runs.
- Earlier invariant violations were tied to missing/duplicate `status` fields and auth semantics. Current spec has `status` and guarded insertion for **CreateOperation**; verify parity for **Modify/Delete**.
