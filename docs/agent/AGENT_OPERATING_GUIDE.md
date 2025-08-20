# AGENT\_OPERATING\_GUIDE.md (Concise vNext)

> **Scope:** How every agent works in this repo. Keep decisions constitutional, verified, observable, and fast.
> **Hard limit:** This file must stay **< 8k chars**.

---

## 1) Mission & Principles

**Mission:** Build the Constitutional AI stack using Synthetic Memory Graphs (SMGs) that **represent** (not replicate) human preferences while preserving sovereignty.

**North stars (must hold):**

1. **Sovereignty** — no unauthorized actions.
2. **Capability** — assist, don’t replace.
3. **Transparency** — explain impact, leave traces.
4. **Revocation** — user can undo/override.

**Stack targets:** PostgreSQL · Neo4j · Qdrant · MinIO (+ Redis optional).

---

## 2) Ownership Boundaries (do/don’t)

**TLA-owned (hands off):**

* Verification specs, runners & schedules.
* `verification/**`, `.tla/.cfg` files.
* Edits to this guide require **`owner:guide-ok`**.

**Implementation-owned (you do):**

* Product/infra code, scripts, CI policy gates.
* Audit receipts, non-TLA docs and benches.

If unsure → don’t touch; ask or open an issue.

---

## 3) Verification & CI Policy

**Classes**

* **Class A (\~10m):** core safety for PRs.
* **Class B (nightly):** broader coverage.
* **Class C (weekly):** compositional/distributed.

**CI rules**

* Every PR runs **Class A**; fail on regression or missing artifacts.
* “Status-only” PRs: **no `.tla/.cfg` diffs**.
* Non-TLA agents **must not** add/modify/remove TLA verification jobs.

**Artifacts (append-only)**

* TLA logs → `docs/_archive/tla_logs/` (timestamp + short README).
* Audit receipts → `docs/audit/...`.

---

## 4) Performance SLOs (guardrails)

* Neo4j constitutional validation **p95 < 170 ms**.
* Anchor transform **p95 < 100 ms**.
* Qdrant search **p95 ≤ 10 ms** (dev receipts acceptable; track trend).

Any risk to SLOs → include a perf note + receipt under `docs/audit/...`.

---

## 5) Labels & Tracking (policy-gates)

**Required per PR/issue**

* **Exactly one:** `type:*` (feature|bug|docs|refactor|enhancement|research|epic)
* **Exactly one:** `status:*` (discussion|in-progress|in-review|blocked|done)
* **Exactly one:** `priority:*` (high|medium|low)
* **≥1:** `area:*` (backend|infra|devops|docs|ui|frontend|security|chatbot|…)

**Forbidden labels:** `deferred`, `status:review`, `blocked: adr-pipeline`.

**Do not create labels from CI/scripts.** Use the GitHub UI.

**Branch protection (admin UI):** require status checks
`policy-gates` and `policy-guide-ownership`.

---

## 6) PR Lifecycle (checklist)

**Before open**

* ✅ Class A green (or BITE explained).
* ✅ `pre-commit run -a` clean.
* ✅ Required labels set; link issue(s).
* ✅ Receipts/docs added where relevant.

**During review**

* ✅ CI green (tests + TLA jobs visible).
* ✅ No `.tla/.cfg` in **status-only** PRs.
* ✅ Perf receipts for perf-sensitive changes.

**Merge**

* Prefer **squash** with conventional commits (`feat(x): …`, `fix(y): …`).

---

## 7) Worktrees & Isolation (avoid stepping on TLA)

**Pattern**

* Keep your TLA workspace untouched.
* Create a **clean mirror**: detached worktree at `origin/main` (e.g., `~/wt/main-impl`).
* For changes, create a **feature worktree/branch** (one per stream).

**Recovery**

* If a worktree path exists without `.git`: remove the folder, `git worktree prune`, re-add.
* Never switch branches or stash in the TLA workspace to fix your own work.

---

## 8) Repo Hygiene & Paths

* **Pre-commit hooks:** YAML/EOF/trailing-ws + Black + Ruff.
* **Excluded from hooks:** `var/`, `docs/automation/ingestion_output/`.
* **Python shim:** `tools/shim/python` (`.venv/bin/python` → `python3` fallback).

**Where to put things**

* TLA logs: `docs/_archive/tla_logs/<YYYYMMDD-HHMM>/…`
* Audit receipts: `docs/audit/<stream>/<YYYYMMDD-HHMM>/…/*.json`
* Don’t commit: `var/**` (local drafts/temp outputs).

---

## 9) Local Neo4j (dev convenience)

* Default env: `NEO4J_URI=bolt://localhost:7687`, `NEO4J_USER=neo4j`, `NEO4J_PASSWORD=please_set_me`.
* Use a detached container for dev; stop when done.
* Seed helper exists (`scripts/seed_neo4j.py`) and is **idempotent**.

**Quiet logs principle:** On fresh DBs, skip graph MATCH if core labels are missing to avoid UnknownLabel noise (engine implements this).

---

## 10) Observability & Receipts

For benches/validation, emit compact JSON receipts with:

* sample counts, p50/p95/max/avg ms, target ms
* feature flags (e.g., `neo4j_enabled`)
* timestamped directory under `docs/audit/<stream>/…`

Reference key receipts in PR bodies.

---

## 11) Constitutional Validation (every feature)

Keep/implement a guard that enforces the four North stars and returns a typed failure with an audit trail (never “best effort” past a red flag).

---

## 12) Definition of Done

* Class A green.
* Labels compliant.
* Docs updated if public behavior/SLOs affected.
* Receipts present (perf/security/verification relevant).
* Architect note in PR if trade-offs were made.

---

## 13) Risks & Mitigations

* **Tooling drift (JDK/TLA):** CI must fail fast with clear messages.
* **Spec creep in status-only PRs:** gate `.tla/.cfg` diffs.
* **Validator strictness:** handle missing keys gracefully; log error paths.
* **Worktree rot:** prune & recreate; never operate from TLA workspace.

---

## 14) Output Conventions (UI-first, Script-second)

* Start with a short **READ ME FIRST** + bullet **ACTIONS**.
* Provide terminal steps under **“OPTIONAL: TERMINAL SCRIPT”** (≤200 lines; idempotent).
* Every ops deliverable is dual-mode:

  * (A) human summary (decisions, risks, exact file paths),
  * (B) copy-paste script to do the work.
* Use explicit sections: **READ ME FIRST**, **ACTIONS**, **RISKS**, **ARTIFACTS**, **OPTIONAL: TERMINAL SCRIPT**.
* Don’t auto-execute or imply background work.

---

## 15) Quick References

* Operating guide (this file): `docs/agent/AGENT_OPERATING_GUIDE.md`
* Policy gates (CI): `.github/workflows/policy-gates.yml`
* Guide ownership gate: `.github/workflows/policy-guide-ownership.yml`
* Protected doc: `docs/agent/AGENT_OPERATING_GUIDE.md`
* Example receipts: `docs/audit/streams12/20250819-150429/{validation.json,qdrant_bench.json}`

---
