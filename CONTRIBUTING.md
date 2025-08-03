# Contributing Guide

Welcome! We follow **Conventional Commits 1.0** and a structured GitHub‑Issues workflow.
Please skim this file before opening PRs or issues.

---

## 1. Commit Message Rules

Use the template below (auto‑injected by Git):

```text
# <type>(<scope>): <subject>
#
# TYPES
#   feat      – new feature
#   fix       – bug fix
#   docs      – documentation only
#   style     – formatting (no code change)
#   refactor  – code improvement (no feature/bug)
#   perf      – performance boost
#   test      – adding / updating tests
#   chore     – tooling / build tasks
#
# WHY  – 1‑2 sentences (wrap ≤72 chars)
# HOW  – optional implementation notes / trade‑offs
#
# BREAKING CHANGE: <impact & migration>
#
# References: Closes #123 · Relates owner/repo#456
# Meta: Co‑authored‑by: Name <email>
# Follows Conventional Commits 1.0.
```

### Quick checklist

* **Subject ≤ 50 chars**, imperative mood, no period.
* Use `feat`/`fix` to trigger semantic‑release bumps (future).
* Link issues with `Closes #id` – CI auto‑closes on merge.

> 🚦 `commitlint` + Husky enforce these rules locally and in CI.

---

## 2. Issue Lifecycle & Labels

Each issue **must** include at least one label from every column:

| Priority          | Type                                        | Status                              | Area                                         | Effort         |
| ----------------- | ------------------------------------------- | ----------------------------------- | -------------------------------------------- | -------------- |
| `priority:high`   | `type:feature`<br>`type:bug`<br>`type:docs` | `status:discussion`                 | `area:ui`                                    | `effort:large` |
| `priority:medium` | `type:refactor`<br>`type:research`          | `status:in-progress`                | `area:backend`                               |                |
| `priority:low`    | `type:enhancement`                          | `status:blocked`<br>`status:review` | `area:docs`<br>`area:color`<br>`area:devops` |                |
|                   |                                             | `status:done`                       | `area:chatbot`                               |                |

### Issue template

```
## Goal

### Tasks
- [ ]

### Acceptance Criteria
```

* Use `🔗 This issue depends on #<id>` for dependencies.
* Edit existing issues with `gh issue edit`, don’t duplicate.

---

## 3. Local Git Hooks

| Hook           | Tool        | Purpose                           |
| -------------- | ----------- | --------------------------------- |
| **pre‑commit** | lint‑staged | ESLint & Prettier on staged files |
| **commit‑msg** | commitlint  | Enforce template above            |
| **pre‑push**   | Jest & lint | Run full test suite + lint        |

Setup is automatic via `npm install` (Husky prepare script). If hooks are missing, run:

```bash
npx husky install
```

---

## 4. CI Pipeline (GitHub Actions)

CI runs on every push / PR to **main**:

1. 📝 Commitlint
2. 🧹 Lint
3. 🛡️  Type‑check
4. 🧪 Tests
5. 🏗️  Build (Next.js)

Pushes with failing checks are blocked from merge.

---

## 5. Coding Standards

* Use TypeScript strict mode.
* Run `npm run lint --fix` before committing large refactors.
* Prefer small, focused PRs (< 400 lines changed).

---

Happy hacking! ✨
