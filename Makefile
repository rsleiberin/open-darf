.PHONY: bench-all aggregate accept verify-splits bootstrap

bench-all:
	./scripts/phase7i/run_all.sh --split=test

aggregate:
	./scripts/phase7i/aggregate_scoreboard.py

accept:
	./scripts/phase7i/acceptance_check.py

verify-splits:
	./scripts/phase7i/verify_splits.py

bootstrap:
	./scripts/phase7i/datasets_bootstrap.sh
