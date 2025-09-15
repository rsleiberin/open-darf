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

archive-receipts:
	./scripts/phase7i/receipts_archive.sh

reset-for-real: archive-receipts
	@echo "[RESET] Archived current receipts. Next:"
	@echo "  1) Edit scripts/phase7i/runner_cmds.env to point to REAL models"
	@echo "  2) make runners-verify"
	@echo "  3) make bench-test && make aggregate && make accept && make gate"

## Phase 7I — quick loop on test split
bench-test:
	@./scripts/phase7i/run_all.sh --split=test

.PHONY: aggregate-phase7s
aggregate-phase7s:
\t./scripts/phase7s/aggregate_evidence.sh

.PHONY: intake-community
intake-community:
\tbash scripts/phase7s/intake_evidence.sh $(files)

.PHONY: clean-artifacts
clean-artifacts:
\t@echo "[clean] removing evidence, receipts, bundles under var/ and open-darf/"
\t@rm -rf var/reports var/receipts var/releases
\t@rm -rf open-darf/var
\t@rm -f open-darf/open-darf-report-*.tar.gz ./open-darf-report-*.tar.gz
\t@echo "[clean] done"
