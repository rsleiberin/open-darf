# Session Checklist — Impl Agent (Stream-1 P2)

- [ ] Recover terminal & confirm repo root (`git rev-parse`, `pwd`)
- [ ] Create recovery branch
- [ ] Fix Python typing error (replace `Dict[...] | None` with `Optional[...]`)
- [ ] Repair `apps/api/http.py` `/validate` route
- [ ] Ensure receipts + metrics calls are no-throw
- [ ] Add/verify tests (route, metrics, reason-codes, optional indexes)
- [ ] Tighten Phase-2 CI workflow (cache + path filters)
- [ ] Install local deps & run tests (pytest)
- [ ] Commit & push branch
- [ ] Open PR with labels
- [ ] Make Phase-2 check REQUIRED on `main` (GitHub UI)
- [ ] Merge PR (squash), auto-merge if checks pending
- [ ] Prune remotes/branches (`git fetch --prune`, `git remote prune origin`)
- [ ] Verify clean repo state (`git status -sb`, `git branch -r`)
- [ ] Update CHANGELOG if needed

> End-of-session target: **changes pushed**, **PR merged (or auto-merge armed)**, repo **clean/pruned**.
