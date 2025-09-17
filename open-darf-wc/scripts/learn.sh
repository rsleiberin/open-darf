#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
printf "===\n===\n===\n"
echo "=== Open-DARF · Learning Module (Linux) ==="
for f in docs/learning/lesson_01_introduction.md docs/learning/lesson_02_docker_stack.md docs/learning/lesson_03_constitutional_ai.md; do
  echo
  echo "---- $(basename "$f") ----"
  sed -n '1,80p' "$f" | sed -e 's/^# .*$/[Lesson]/'
done
echo
echo "[✓] More: open docs/learning/* in your editor."
