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

## Remove Zone.Identifier metadata from repo
## Full docs cycle: ingest → ADR generation
## Remove Zone.Identifier metadata from repo
## Full docs cycle: ingest → ADR generation
# ----------------------------
# Documentation & Repo Hygiene
# ----------------------------

## Run document ingestion pipeline
## Remove Zone.Identifier metadata from repo
## Full docs cycle: ingest → ADR generation

# ----------------------------
# Documentation & Repo Hygiene
# ----------------------------

## Run document ingestion pipeline
docs-ingest:
	@bash tools/document-ingestion.sh

## Remove Zone.Identifier metadata from repo
clean-zone:
	@bash tools/remove-zone-identifiers.sh

## Full docs cycle: ingest → ADR generation
docs-full:
	@bash tools/document-ingestion.sh
	@bash tools/generate-adrs.sh
# Dev DB helpers
db-up:      ; @tools/dev/pg-dev.sh db-up
db-psql:    ; @tools/dev/pg-dev.sh db-psql
db-down:    ; @tools/dev/pg-dev.sh db-down
db-logs:    ; @tools/dev/pg-dev.sh db-logs
test-db:    ; @tools/dev/pg-dev.sh test-db

.PHONY: rel-demo
rel-demo:
\t@mkdir -p var/receipts/phase6c/validation
\t@echo '{"doc_id":"D1","entities":[{"id":"A","type":"Gene","sent":0},{"id":"B","type":"Disease","sent":0}],"relations":[{"head":"A","tail":"B","type":"assoc"}]}' > var/receipts/phase6c/validation/toy_biored.jsonl
\t@PYTHONPATH=$(PWD)$(if $(PYTHONPATH),:$(PYTHONPATH),) \
\tpython3 -m scripts.relation_extraction.emit_rel_metrics --input var/receipts/phase6c/validation/toy_biored.jsonl --out var/receipts/phase6c/validation/biored_relations_scores_heuristic.json --predictor heuristic
\t@echo 'biored metrics:'
\t@jq '.biored' var/receipts/phase6c/validation/biored_relations_scores_heuristic.json
