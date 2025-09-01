# GitHub Operations for Implementation Agent

## Issue Management
- Create issues using templates from docs/implementation/
- Label format: type:*, status:*, priority:*, area:*
- Link PRs to issues with "Fixes #XXX"
- Never create labels from scripts

## PR Workflow
1. Create feature branch: `git checkout -b type/description`
2. Commit with conventional format: `feat(scope): message`
3. Push and create PR with required labels
4. Squash merge preferred

## Required Labels (exactly one each)
- type: feature|bug|docs|refactor|enhancement|research|epic
- status: discussion|in-progress|in-review|blocked|done
- priority: high|medium|low
- area: backend|infra|devops|docs|ui|frontend|security|chatbot

## Forbidden
- deferred, status:review, blocked:adr-pipeline labels
- Modifying .tla/.cfg files
- Direct pushes to main
