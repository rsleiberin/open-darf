# Implementation Handoff — Phase 7G

**Date (UTC):** 2025-09-07T23:10:53Z  
**From:** Implementation Agent (current)  
**To:** Implementation Agent (next)  
**Branches/PRs:**  
- `feat/phase7g-relation-baseline` (PR #384) — heuristic baseline v6 best; E1 PASS  
- `feat/phase7g-config` (PR #385) — config & CI; packaging smoke; **7G-PKG-E1 PASS**  
- `feat/phase7g-pure-baseline` (PR #386) — PURE plan + harness skeleton + enablement v0

## Current State
- **Neo4j**: 5.22.0, A1 indexes ONLINE (see preflight receipts).
- **Baseline RE (SciERC-dev)**: v6 P/R/F1 0.457/0.267/0.337; compliance=1.0; receipts under `var/receipts/phase7g/relation_baseline/run/`.
- **CI Gates**: Config validate; RE smoke (F1≥0.20 & compliance≥0.95); packaging smoke; E2E bootstrap.

## What’s Next (Priority)
1. **PURE enablement (opt-in)**  
   - Add label **`ci:run-pure`** to PR #386 to run opt-in workflow.  
   - If green, proceed to implement inference in `apps/relex/pure/runner.py`.
2. **E2 Targets**  
   - Aim **F1 ≥ 0.50** on SciERC-dev; emit receipts in `var/receipts/phase7g/pure_runs/<ts>/`.
3. **Secrets & Profiles**  
   - If promoting to staging/prod, move DB/LLM secrets to Docker/Vault (compose examples in CONFIG.md).

## Receipts (Pointers)
See `docs/phase7g/RECEIPTS_INDEX.md` for a consolidated list.

## Risks
- Heavy deps churn; keep CI green by respecting deps-missing/skip semantics.

