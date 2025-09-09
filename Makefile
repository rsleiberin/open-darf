.PHONY: bench-all aggregate accept verify-splits bootstrap

bench-all: preflight 
	./scripts/phase7i/run_all.sh --split=test

aggregate:
	./scripts/phase7i/aggregate_scoreboard.py

accept:
	./scripts/phase7i/acceptance_check.py

verify-splits:
	./scripts/phase7i/verify_splits.py

bootstrap:
	./scripts/phase7i/datasets_bootstrap.sh

preflight:
	./scripts/phase7i/preflight.sh

handoff:
	./scripts/phase7i/acceptance_check.py > /dev/null || true
	./scripts/phase7i/aggregate_scoreboard.py > /dev/null || true
	./scripts/phase7i/verify_splits.py --json > /dev/null || true
	@echo "Regenerating session handoff..."
	@true

gate:
	./scripts/phase7i/acceptance_gate.sh

runners-verify:
	./scripts/phase7i/verify_runners.sh

doctor:
	./scripts/phase7i/doctor.sh
