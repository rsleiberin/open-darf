# Branch & PR Workflow
1. `git checkout main && git pull`
2. `git checkout -b <type>/<slug>`  # feat|fix|chore|docs
3. Work → `git commit -m "type(scope): msg"`
4. `git push -u origin <branch>`
5. `gh pr create --fill`
6. Wait for CI, get 1 approval, merge via PR

### Rebase-first rule  (added 2025-08-06)

* Feature branches **must be rebased onto `origin/main` before every push**.  
  A pre-push hook blocks out-of-date branches.

* `git pull` defaults to `--rebase` (see `.gitconfig.example`).
