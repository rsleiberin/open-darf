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
	./scripts/phase7s/aggregate_evidence.sh

.PHONY: intake-community
intake-community:
	bash scripts/phase7s/intake_evidence.sh $(files)

.PHONY: clean-artifacts
clean-artifacts:
	@rm -rf community_intake/{queue,accepted,rejected}/* 2>/dev/null || true
	@echo "[clean] removing evidence, receipts, bundles under var/ and open-darf/"
	@rm -rf var/reports var/receipts var/releases
	@rm -rf open-darf/var
	@rm -f open-darf/open-darf-report-*.tar.gz ./open-darf-report-*.tar.gz
	@echo "[clean] done"

.PHONY: finalize-phase7s
finalize-phase7s:
	@bash scripts/phase7s/finalize.sh

.PHONY: acceptance-phase7s
acceptance-phase7s:
	@bash scripts/phase7s/acceptance_status.sh

.PHONY: review-packet
review-packet:
	@bash scripts/phase7s/build_review_packet.sh
