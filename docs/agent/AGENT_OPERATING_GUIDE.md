# AGENT\_OPERATING\_GUIDE.md (Concise vNext)

> **Scope:** How every agent works in this repo. Keep decisions constitutional, verified, observable, fast.
> **Hard limit:** This file must stay **< 8k chars**.

---

## 1) Mission & Principles

**Mission:** Build the Constitutional AI stack using SMGs that **represent** (not replicate) human preferences while preserving sovereignty.

**North stars:** (1) **Sovereignty** — no unauthorized actions; (2) **Capability** — assist, don’t replace; (3) **Transparency** — explain impact, leave traces; (4) **Revocation** — user can undo/override.

**Stack targets:** PostgreSQL · Neo4j · Qdrant · MinIO (+ optional Redis).

---

## 2) Ownership Boundaries

**TLA-owned (hands off):** verification specs/runners/schedules; `verification/**`, `.tla/.cfg`; edits here require **`owner:guide-ok`**.
**Implementation-owned (you do):** product/infra code, scripts, CI policy gates; audit receipts; non-TLA docs/benches.

> If unsure → don’t touch; ask or open an issue.

---

## 3) Verification & CI

**Classes:** A (\~10m core), B (nightly), C (weekly).
**Rules:** every PR runs **Class A**; fail on regression/missing artifacts; “status-only” PRs: **no `.tla/.cfg` diffs**; non-TLA agents don’t change TLA jobs; prefer **phase-scoped** jobs (no live services unless required).
**Artifacts (append-only):** TLA logs → `docs/_archive/tla_logs/`; audit receipts → `docs/audit/...`.

---

## 4) Performance SLOs

Neo4j constitutional **p95 < 170 ms**; Anchor transform **p95 < 100 ms**; Qdrant search **p95 ≤ 10 ms** (dev receipts OK; track trend).

> Risk to SLOs → include perf note + receipt in `docs/audit/...`.

---

## 5) Labels & Tracking (policy gates)

Per PR/issue: **exactly one** `type:*` (feature|bug|docs|refactor|enhancement|research|epic), **exactly one** `status:*` (discussion|in-progress|in-review|blocked|done), **exactly one** `priority:*` (high|medium|low), and **≥1** `area:*` (backend|infra|devops|docs|ui|frontend|security|chatbot|…).
**Forbidden:** `deferred`, `status:review`, `blocked: adr-pipeline`.
Do **not** create labels from CI/scripts. Require checks: `policy-gates`, `policy-guide-ownership`.

---

## 6) PR Lifecycle (checklist)

**Before open:** Class A green (or BITE explained); `pre-commit run -a` clean; required labels set; link issues; receipts/docs present.
**During review:** CI green; no `.tla/.cfg` in **status-only** PRs; perf receipts for perf-sensitive changes.
**Merge:** prefer **squash** with conventional commits (`feat(x): …`, `fix(y): …`).

---

## 7) Worktrees & Isolation

Keep TLA workspace untouched. Create a clean mirror at `origin/main` (e.g., `~/wt/main-impl`); do work on feature branches.
**Recovery:** if a path lost `.git`, remove folder → `git worktree prune` → re-add. Don’t switch branches or stash inside the TLA workspace.

---

## 8) Repo Hygiene & Paths

**Hooks:** YAML/EOF/trailing-ws + Black + Ruff.
**Excluded:** `var/`, `docs/automation/ingestion_output/`.
**Python shim:** `tools/shim/python` (`.venv/bin/python`→`python3` fallback).

**Paths:** TLA logs → `docs/_archive/tla_logs/<YYYYMMDD-HHMM>/…`; audit receipts → `docs/audit/<stream>/<YYYYMMDD-HHMM>/…/*.json`. Don’t commit `var/**`.

**Shell heredocs (ops scripts):** use **UPPER\_SNAKE** markers (e.g., `PHASE2_WIRE_240`); one logical step per heredoc; idempotent; echo banners.

**OpenAI UI / backticks:** agents must provide **copy/paste-safe** bash. Wrap the **message** and the **initial** bash block in triple backticks; **never place backticks inside heredocs** (the UI will break them).

---

## 9) Local Neo4j (dev convenience)

`NEO4J_URI=bolt://localhost:7687`, `NEO4J_USER=neo4j`, `NEO4J_PASSWORD=please_set_me`. Use a detached container and stop when done. Seed via `scripts/seed_neo4j.py` (idempotent).
**Quiet logs:** on fresh DBs, skip MATCH if core labels missing to avoid UnknownLabel noise.

---

## 10) Observability & Receipts

**Benches/validation receipts:** sample counts, p50/p95/max/avg ms, targets; feature flags (e.g., `neo4j_enabled`); timestamped under `docs/audit/<stream>/…`. Reference receipts in PR bodies.
**Runtime signals:** structured log lines (e.g., `decision=<…> reason=<…>`), counters for critical outcomes; never let observability paths raise.

---

## 11) Constitutional Validation

Every capability passes a **constitutional guard**: resolve to `ALLOW|DENY|INDETERMINATE` with a machine-readable `reason_code`; **deny precedence**; **fail-closed** on uncertainty; keep audit trail; experimental paths are **env-gated**.

---

## 12) Definition of Done

Class A green; labels compliant; docs updated when behavior/SLOs affected; relevant receipts present; architect note in PR for trade-offs.

---

## 13) Risks & Mitigations

Tooling drift (JDK/TLA) → CI fails fast; status-only spec creep → gate `.tla/.cfg` diffs; validator strictness → handle missing keys gracefully; worktree rot → prune & recreate; avoid live-service coupling—prefer phase-scoped tests.

---

## 14) Turn Format: Progress Bar + Checklist Protocol

**Source of truth:** the **architect-provided session checklist** (latest handoff). Do **not** reword/reorder it.

**Progress bar (line 1 of every message):** groups separated by `|`, one token per checklist item; order **fixed** after first render.

**Tokens:**
🟨 Not started · 🟧 In progress · 🟩 Done · 🟥 Blocked · 🟦 Pending review/verification · 🟪 Waiting on external/decision
(Use 🟦/🟪 only when helpful; otherwise stick to 🟨/🟧/🟩/🟥.)

**Message 1 template**

```
<progress bar, e.g.>
🟨🟨🟨🟨 | 🟨🟨🟨 | 🟨🟨

<PASTE THE ARCHITECT CHECKLIST VERBATIM — grouped and ordered exactly as given>
Group 1 — <title> (N)
- <item 1>
- <item 2>
…
```

**Message 2+ template**

```
<progress bar only>
🟨🟧🟨 | 🟦🟨🟨

<your commands/results for the step>
```

**Commands:** prefer a **single** bash heredoc per step; idempotent; CI remains service-free; perf tests live in `tests/performance/` and are gated with `RUN_PERF=1`. Receipts: write to tmp by default; mirror into `docs/audit/_last/` only when `WRITE_RECEIPTS=1` **and** not CI.

---

## 15) Session Discipline

If a terminal crashes, provide a concise **resume script** on request. Never run background tasks or promise future work—**perform in-message**. Keep env overrides explicit; **`ENGINE_FAIL_OPEN` is dev-only** and forbidden in CI/prod (ignore/clear, fail-closed).

---

## 16) Quick References

* This guide: `docs/agent/AGENT_OPERATING_GUIDE.md`
* Policy gates: `.github/workflows/policy-gates.yml`
* Guide ownership gate: `.github/workflows/policy-guide-ownership.yml`
* Protected doc: `docs/agent/AGENT_OPERATING_GUIDE.md`
* Example receipts: `docs/audit/streams12/20250819-150429/{validation.json,qdrant_bench.json}`

---
