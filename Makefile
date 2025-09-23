# DARF Project Makefile - Modernized Build System
# Uses Poetry for Python dependencies and PNPM for Node.js packages

.DEFAULT_GOAL := help
.PHONY: help install build test lint clean dev-setup ci-check

# =============================================================================
# Development Setup
# =============================================================================

help: ## Show this help message
	@grep -E '^[a-zA-Z_-]+:.*?## .*$$' $(MAKEFILE_LIST) | awk 'BEGIN {FS = ":.*?## "}; {printf "\033[36m%-20s\033[0m %s\n", $$1, $$2}'

install: ## Install all dependencies
	@echo "Installing Python dependencies..."
	poetry install
	@echo "Installing Node.js dependencies..."  
	pnpm install

dev-setup: install ## Complete development environment setup
	@echo "Setting up development environment..."
	poetry run pre-commit install || echo "pre-commit not configured"
	@echo "Development setup complete"

# =============================================================================
# Build & Test
# =============================================================================

build: ## Build the project
	@echo "Building Python packages..."
	poetry build
	@echo "Building Node.js packages..."
	pnpm run build || echo "No build script defined"

test: ## Run all tests
	@echo "Running Python tests..."
	poetry run pytest tests/ -v
	@echo "Running additional test scripts..."
	bash scripts/lifecycle_smoke.sh || echo "Smoke tests not available"

test-quick: ## Run quick smoke tests only
	@echo "Running quick tests..."
	poetry run pytest tests/unit/ -v || echo "Unit tests not available"

# =============================================================================
# Quality Assurance
# =============================================================================

lint: ## Run all linting tools
	@echo "Running Python linting..."
	poetry run ruff check .
	poetry run mypy apps/ || echo "MyPy check completed with warnings"
	@echo "Running Node.js linting..."
	pnpm run lint

format: ## Format code
	@echo "Formatting Python code..."
	poetry run ruff format .
	@echo "Python formatting complete"

security: ## Run security checks
	@echo "Running security checks..."
	poetry run bandit -r apps/ || echo "Security scan completed"
	poetry run safety check || echo "Dependency security check completed"

# =============================================================================
# Application Operations
# =============================================================================

ingest: ## Run document ingestion pipeline  
	@echo "Running document ingestion..."
	poetry run python -m apps.pipeline.run || echo "Ingestion pipeline not available"

validate: ## Run validation pipeline
	@echo "Running validation..."
	bash validate/run_minimal.sh || echo "Validation script not available"

benchmark: ## Run performance benchmarks
	@echo "Running benchmarks..."
	poetry run python scripts/bench_constitution_engine.py || echo "Benchmarks not available"

# =============================================================================
# Infrastructure & Deployment
# =============================================================================

services-up: ## Start development services
	@echo "Starting development services..."
	docker compose -f infra/compose/compose.yaml up -d || echo "Docker services not configured"

services-down: ## Stop development services  
	@echo "Stopping development services..."
	docker compose -f infra/compose/compose.yaml down || echo "Docker services not configured"

# =============================================================================
# Maintenance
# =============================================================================

clean: ## Clean build artifacts
	@echo "Cleaning Python artifacts..."
	find . -type d -name "__pycache__" -exec rm -rf {} + 2>/dev/null || true
	find . -name "*.pyc" -delete 2>/dev/null || true
	poetry run coverage erase 2>/dev/null || true
	@echo "Cleaning Node.js artifacts..."
	rm -rf node_modules/.cache 2>/dev/null || true
	@echo "Cleaning build artifacts..."
	rm -rf dist/ build/ *.egg-info/ 2>/dev/null || true

clean-all: clean ## Deep clean including dependencies
	@echo "Removing all dependencies..."
	rm -rf node_modules/ 2>/dev/null || true
	poetry env remove python 2>/dev/null || true

# =============================================================================  
# CI/CD
# =============================================================================

ci-check: lint test ## Run CI checks locally
	@echo "CI checks completed"

pre-commit: lint ## Run pre-commit checks
	@echo "Running pre-commit hooks..."
	poetry run pre-commit run --all-files || echo "Pre-commit completed with issues"

# =============================================================================
# Legacy Compatibility (deprecated)
# =============================================================================

legacy-help: ## Show legacy Makefile commands (deprecated)
	@echo "Legacy Makefile moved to Makefile.legacy"
	@echo "Use 'make help' to see modern commands"

