# Session Checklist — Impl Agent (Stream-1 P2)

- [x] Recover terminal & confirm repo root (`git rev-parse`, `pwd`)
- [x] Create recovery branch
- [x] Fix Python typing error (replace `Dict[...] | None` with `Optional[...]`)
- [x] Repair `apps/api/http.py` `/validate` route
- [x] Ensure receipts + metrics calls are no-throw (dynamic env path for receipts)
- [x] Add/verify tests (route, metrics, reason-codes, optional indexes)
- [x] Tighten Phase-2 CI workflow (cache + path filters)
- [x] Install local deps & run tests (pytest)
- [x] Commit & push branch
- [x] Open PR with labels (current PR is this recover branch)
- [ ] Make Phase-2 check REQUIRED on `main` (GitHub UI)
- [ ] Merge PR (squash) or enable auto-merge and wait for checks
- [ ] Prune remotes/branches (`git fetch --prune`, `git remote prune origin`)
- [ ] Verify clean repo state (`git status -sb`, `git branch -r`)
- [ ] Update CHANGELOG if needed

> End-of-session target: **changes pushed**, **PR merged (or auto-merge armed)**, repo **clean/pruned**.
