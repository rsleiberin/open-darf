#!/usr/bin/env bash
# Synchronise the “Sane Label Schema” with this repository.
# Usage:  chmod +x tools/sync-labels.sh && ./tools/sync-labels.sh
set -euo pipefail

REPO="rsleiberin/darf-source"   # change only if you rename / fork

# name|description|hexColour   (23 rows — keep exact format)
while IFS='|' read -r NAME DESC COLOR; do
  printf "🔧 %-20s … " "$NAME"
  if gh label edit "$NAME" -R "$REPO" --color "$COLOR" --description "$DESC" >/dev/null 2>&1
  then echo "updated"
  else gh label create "$NAME" -R "$REPO" --color "$COLOR" --description "$DESC" >/dev/null && echo "created"
  fi
done <<'LABELS'
good first issue|Good for newcomers|7057ff
help wanted|Extra attention is needed|008672
priority:high|Urgent fix/feature|d73a4a
priority:medium|Normal priority|f9d0c4
priority:low|Can be deferred|bfe5bf
type:feature|New functionality|006b75
type:bug|Broken behaviour|d73a4a
type:docs|Documentation work|c2e0c6
type:refactor|Code improvements without feature changes|bfe5bf
type:enhancement|Enhancements or small improvements|0e8a16
type:research|Exploratory spike|5319e7
status:discussion|Needs approach discussion|5319e7
status:in-progress|Being implemented|1d76db
status:blocked|Blocked by dependency|ff9f1c
status:review|Awaiting code review|fbca04
status:done|Completed|3c3c3c
area:backend|Server side or integration|207de5
area:devops|Deployment & environment|0e8a16
area:ui|Frontend UI / styling|5319e7
area:chatbot|Chatbot / AI|ededed
area:color|Colour / design tokens|ff7f50
area:docs|Documentation tasks|00d4ff
area:infra|CI/CD & infrastructure|207de5
LABELS

# prune GitHub default labels we never use
for UNUSED in bug enhancement documentation duplicate invalid question wontfix; do
  if gh label delete "$UNUSED" -R "$REPO" --yes >/dev/null 2>&1; then
    echo "🗑️  removed $UNUSED"
  fi
done
echo "✅  Label schema synced."
