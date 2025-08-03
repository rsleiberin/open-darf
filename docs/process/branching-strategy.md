# Branch & PR Workflow
1. `git checkout main && git pull`
2. `git checkout -b <type>/<slug>`  # feat|fix|chore|docs
3. Work → `git commit -m "type(scope): msg"`
4. `git push -u origin <branch>`
5. `gh pr create --fill`
6. Wait for CI, get 1 approval, merge via PR
