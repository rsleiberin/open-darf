.PHONY: help lint fix test scan clean

VENV = poetry run

help:  ## Show available targets
@grep -E '^[a-zA-Z_-]+:.*?## .*$$' $(MAKEFILE_LIST) | sort | \
  awk 'BEGIN {FS = ":.*?## "}; {printf "\033[36m%-10s\033[0m %s\n", $$1, $$2}'

lint: ## Run Ruff linter
$(VENV) ruff check .

fix: ## Auto-fix Ruff issues
$(VENV) ruff check --fix .

test: ## Run pytest suite
$(VENV) pytest -q

scan: ## Security scan (Bandit + Safety)
$(VENV) bandit -ll -r apps packages
$(VENV) safety check

clean: ## Remove Python cache files
find . -type f -name '*.py[co]' -delete
find . -type d -name __pycache__ -exec rm -r {} +
