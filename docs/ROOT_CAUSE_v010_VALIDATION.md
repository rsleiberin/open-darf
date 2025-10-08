# Root Cause Analysis — v0.1.0 Validation Pipeline

**Scope:** OpenDARF public subtree (`open-darf/`)  
**Context window:** 2025-10-07 → 2025-10-08

---

## Symptoms Observed
1) Linux generator occasionally crashed terminal sessions.
2) Receipts flagged as “order mismatch” despite being correct.
3) CI showed failing checks for PRs that were otherwise valid.

---

## Direct Causes
1) **Shell interpolation inside Python block**  
   An unquoted heredoc embedded Python that referenced shell vars. The shell expanded those tokens (e.g., `${VAR}`), corrupting the Python code and causing errors like:  
    - bad substitution  
    - unexpected tokens

2) **Sorted key comparison**  
   Validation used `jq keys`, which sorts keys alphabetically. The canonical v0.1.0 requires insertion order. Comparing sorted keys to a canonical ordered list produced false negatives.

3) **Validator exit behavior**  
   Validation exited with a non-zero code on order mismatch. In the interactive UI, this caused the terminal session to end, increasing cognitive load during debugging.

---

## Remediations Implemented
1) **Quoted, env-driven Python writer**  
   The JSON writer was refactored to:
    - Use a quoted heredoc (no shell interpolation).
    - Populate values via environment variables.
    - Preserve canonical order with an ordered structure.

2) **Order-aware JSON validation**  
   Replaced `jq keys` with `jq keys_unsorted` to preserve insertion order.  
   Added a **non-fatal** validator at:
    - `scripts/evidence/validate_receipt_v010.sh`

3) **CI policy update (public)**  
   Updated public workflow `.github/workflows/validation.yml` to:
    - Run the non-fatal validator.
    - Gate on explicit PASS text.
    - Maintain order checks with `keys_unsorted`.

4) **Docs**  
   Added Windows v0.1.0 validation instructions to:
    - `docs/INSTALL-WINDOWS.md`

---

## Verification Evidence
- Fresh Linux receipt created and stored at:  
  `open-darf/var/receipts/open-darf/validation_YYYYMMDD_HHMMSS.json`
- Non-fatal validator output shows:
    - 11 keys
    - key order preserved
    - `receipt_version` = `0.1.0`
    - numeric percentile sanity = OK

---

## Preventive Actions
- Keep validators **non-fatal** in interactive contexts; use CI to enforce PASS.
- Prefer **keys_unsorted** whenever order matters.
- Avoid unquoted heredocs when embedding Python/JSON/YAML.
- Use clean-history sync script for public mirroring to prevent unwanted history exposure.

