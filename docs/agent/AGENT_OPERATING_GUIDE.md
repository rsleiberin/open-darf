# AGENT\_OPERATING\_GUIDE.md (Concise vNext)

> **Scope:** How every agent works in this repo. Keep decisions constitutional, verified, observable, and fast.
> **This file must stay < 8k chars.**

---

## 1) Mission & Principles

* **Mission:** Build the Constitutional AI stack using Synthetic Memory Graphs (SMGs) that **represent** (not replicate) human preferences while preserving sovereignty.
* **North stars (must hold):**

  1. **Sovereignty** (no unauthorized actions)
  2. **Capability** (assist, don’t replace)
  3. **Transparency** (explain impact)
  4. **Revocation** (user can undo/override)
* **Stack targets:** PostgreSQL + Neo4j + Qdrant + MinIO (+ Redis optional).

---

## 2) Verification & CI Policy (TLA+)

* **Classes**

  * **Class A (≈10 min):** Core safety invariants for local dev/PRs.
  * **Class B (≈8 hr):** Broader coverage nightly.
  * **Class C (days):** Compositional/distributed weekly.
* **CI rules**

  * **Every PR:** run **Class A**; **fail PR** on regression or missing artifacts.
  * **Nightly:** **Class B**; publish short status (PASS/BITE) to logs.
  * **Weekly:** **Class C**; attach summary for architect review.
* **Artifacts (write-only; append):**

  * TLA logs: `docs/_archive/tla_logs/` (timestamped filenames + small README).
  * Audit receipts (e.g., perf/validation): `docs/audit/...`
* **No “status-only” PR may change `.tla/.cfg`.** Gate this in CI.

---

## 3) Performance SLOs (guardrails)

* **Neo4j constitutional validation p95 < 170 ms**
* **Anchor transform p95 < 100 ms**
* **Qdrant search p95 ≤ 10 ms** (dev env receipts acceptable; track trend)
* If a change risks SLO, add a perf note + receipt under `docs/audit/…`.

---

## 4) Labels & Tracking (must comply)

* **Required families per issue/PR:**

  * **Exactly one:** `type:*` (feature|bug|docs|refactor|enhancement|research|epic)
  * **Exactly one:** `status:*` (discussion|in-progress|in-review|blocked|done)
  * **Exactly one:** `priority:*` (high|medium|low)
  * **At least one:** `area:*` (backend|infra|devops|docs|ui|frontend|security|chatbot|…)
* **Forbidden:** `deferred`, `status:review`, `blocked: adr-pipeline`.
* Streams & milestones: use `Stream`, `Milestone: M1`, `Roadmap:2025-2026` as appropriate.

---

## 5) PR Lifecycle (checklist)

**Before open**

* ✅ TLA **Class A** green (or explain BITE in negative configs).
* ✅ Pre-commit clean: `pre-commit run -a` (no changed files).
* ✅ Label families set; link issue(s).
* ✅ Artifacts (if relevant) added under approved dirs (see §2, §7).

**During review**

* ✅ CI green (tests + TLA).
* ✅ No `.tla/.cfg` changes in status-only PRs.
* ✅ Docs/SLO receipts included for perf-sensitive changes.

**Merge**

* Prefer **squash** with conventional message (e.g., `feat(search): …`, `fix(api): …`, `chore(ci): …`).

---

## 6) Daily Ops (agent routine)

1. **Sync & triage:** review open PRs; enforce label policy; spot “status-only” claims.
2. **Verification cadence:** confirm last **Class B/C** runs landed logs.
3. **Perf receipts:** if you touched search/validation/transform, drop p95 summary JSON.
4. **Hygiene:** keep local artifacts out of commits; ensure scripts use shim (see §7).

---

## 7) Repo Hygiene & Paths

* **Pre-commit:** YAML/EOF/trailing-ws + Black + Ruff.
* **Excluded from hooks:** `var/`, `docs/automation/ingestion_output/`.
* **Python shim:** `tools/shim/python` (uses `./.venv/bin/python` → `python3`).
* **Where to put things**

  * **TLA logs/status:** `docs/_archive/tla_logs/` (always include short README).
  * **Audit receipts:** `docs/audit/<stream_id>/.../*.json`.
  * **Do not commit:** `var/**` local drafts, temp outputs.

---

## 8) Minimal Runbooks

* **Pre-commit**

  ```bash
  git clean -xdf # if needed
  pre-commit install
  pre-commit run -a
  ```
* **TLA quick status (if scripts exist)**

  ```bash
  bash scripts/tlc_status_classA.sh || echo "no status script"
  bash scripts/run_class_a_now.sh   || echo "no run script"
  # then copy logs into docs/_archive/tla_logs/ with a README
  ```
* **Perf receipt (example Qdrant)**

  * Save JSON under `docs/audit/<stream>/YYYYMMDD-HHMM/…/qdrant_bench.json`.
  * Mention `p95` in PR body.

---

## 9) Constitutional Validation (every feature)

* Add/keep a guard function:

  ```python
  def validate_constitutional_compliance(op, ctx) -> bool:
      return (preserve_user_sovereignty(op, ctx)
              and enhance_user_capability(op, ctx)
              and explain_operation_impact(op, ctx))
  ```
* On violation, raise typed error and **create an audit trail**; never “best effort” past a red flag.

---

## 10) Definition of Done

* Class A green (CI).
* Labels complete; docs updated if public behavior or SLO affected.
* Receipts present (when perf/security/verification relevant).
* Architect-facing note added to PR if tradeoffs were made.

---

## 11) Risks & Mitigations

* **Tooling drift (JDK/TLA):** make CI fail fast with clear message.
* **Spec creep in status drops:** CI rule: reject `.tla/.cfg` diffs in status-only PRs.
* **Validator strictness:** handle missing keys with friendly error; log path in output.

---

## 12) Quick References

* **Operating guide (this file):** `agent/AGENT_OPERATING_GUIDE.md`
* **Status-only PR example:** “Stream 3 — Class-A status-only logs (no spec changes)”
* **Recent receipts:** `docs/audit/streams12/20250819-150429/{validation.json,qdrant_bench.json}`

---

### You are done if:

* PR meets label & CI gates, artifacts are in place, SLOs are respected, and decisions are auditable & constitutional.
