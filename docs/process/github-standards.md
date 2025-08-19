# GitHub Workflow & Repository Standards

This repository **requires** the following conventions for every contributor.

| Concern | Standard |
|---------|----------|
| **Primary branch** | `main` (protected via local *pre-push* hook; direct pushes prohibited) |
| **Commit style**   | [Conventional Commits 1.0.0](https://www.conventionalcommits.org) |
| **PR policy**      | *PR-first*, squash-merge, at least one approving review |
| **Label taxonomy** | [Sane Label Schema](https://github.com/sane-labels/sane-labels) — 23 canonical labels |

---

## 1. Initial repo-setup checklist (once per clone)

| Step | Command |
|------|---------|
| Install pre-commit hooks | poetry run pre-commit install --overwrite |
| Block pushes to `main`   | (provided by `.git/hooks/pre-push` created during bootstrap) |
| Sync Sane labels         | ./tools/sync-labels.sh |
| Clean Zone Identifiers (if cloning from Windows) | ./tools/remove-zone-identifiers.sh |

> **Why label sync?**
> GitHub’s default labels are removed and the canonical 23 Sane labels are created/updated
> so that PR boards, automations and reports remain predictable across all Darf repos.

---

## 2. Branching & naming

* **Feature / fix**   `feat/<slug>`, `fix/<slug>`
* **Docs only**       `docs/<slug>`
* **Chore / infra**   `chore/<slug>`

Always branch from the latest `main`.

---

## 3. Conventional Commit summary

| Type | When to use | Example |
|------|-------------|---------|
| `feat`   | new user-visible functionality | feat(api): add healthcheck endpoint |
| `fix`    | bug or regression               | fix(auth): correct JWT expiry       |
| `docs`   | docs only                       | docs(readme): clarify setup         |
| `chore`  | tooling / infra, no prod code   | chore(ci): upgrade ruff             |
| `refactor` | internal code change, no behaviour | refactor(db): split repo layer |

Conventional Commit scope (text in parentheses) should follow ✨**Sane label areas**✨ (`backend`, `devops`, `docs`, `ui`, …) when practical.

---

## 4. Pull-request checklist

* ✅ CI (pre-commit) passes
* ✅ Conventional title & description
* ✅ Relevant labels applied (at minimum: **type:** ×1, **area:** ×1, **status:in-progress → status:review**)
* ✅ PR linked to an Issue if the change fixes or implements one (Fixes #42)

After squash-merge GitHub auto-deletes the feature branch.

---

## 5. Maintaining the label set

* Script: ./tools/sync-labels.sh
  * idempotent — safe to rerun any time
  * creates/updates **only** the canonical labels
  * deletes default GitHub labels we don’t use (`bug`, `enhancement`, …)

> Run it after forking or enabling Discussions/Issues on a fresh clone.

---

## 6. Zone Identifier Cleanup (WSL + Windows)

Some `.pdf` and `.md` files transferred from Windows may include **Zone.Identifier** metadata streams which can interfere with GitHub Actions and LLM ingestion.

Use this helper script to remove them safely:

./tools/remove-zone-identifiers.sh

Only needed if you’re cloning or editing the repo from a Windows-based editor or terminal.
Last updated: 2025-08-03
