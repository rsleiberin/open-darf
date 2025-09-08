#!/usr/bin/env bash
set -Eeuo pipefail
ROOT="$(git rev-parse --show-toplevel 2>/dev/null || pwd)"
cd "$ROOT"
VENV=".venv_pure"

python3 -m venv "$VENV" 2>/dev/null || python -m venv "$VENV"
. "$VENV/bin/activate"
python -m pip install -U pip wheel

# Prefer CPU wheels for torch to avoid CUDA churn
CPU_INDEX="https://download.pytorch.org/whl/cpu"
pip install --index-url "$CPU_INDEX" torch==2.2.2
pip install -r requirements/pure.txt

echo "=== PURE env ready at $VENV ==="
python -c "import torch, transformers; print({'torch': torch.__version__, 'transformers': __import__('transformers').__version__})"
