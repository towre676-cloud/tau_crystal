SHELL := /usr/bin/env bash

.PHONY: sign manifest sym2 ingest zero interference drift snapshot rewind
sign:
	bash scripts/ci/signed_runner.sh

manifest:
	bash scripts/meta/validate_manifest_tree.sh

ingest:
	@[ -n "$(CURVE)" ] && [ -n "$(SRC)" ] || (echo "usage: make ingest CURVE=37a1 SRC=path/to/local_factors.json"; exit 2)
	bash scripts/langlands/ingest_local_factors.sh "$(CURVE)" "$(SRC)"

zero:
	@[ -n "$(CURVE)" ] || (echo "usage: make zero CURVE=37a1"; exit 2)
	bash scripts/langlands/run_zero_check.sh "$(CURVE)"

interference:
	@[ -n "$(A)" ] && [ -n "$(B)" ] || (echo "usage: make interference A=a.csv B=b.csv [W=10]"; exit 2)
	bash scripts/interference/build_interference_map.sh "$(A)" "$(B)" "$(W)"

drift:
	bash scripts/interference/compare_to_baseline.sh

snapshot:
	bash scripts/timefold/snapshot_state.sh "$(L)"

rewind:
	bash scripts/timefold/rewind_to_snapshot.sh "$(S)" "$(L)"
entropy:
	bash scripts/entropy/witness_entropy_score.sh
# === Entropy quick ===
GLOB ?=
LIMIT ?=
.PHONY: entropy-quick
entropy-quick:
	@bash scripts/entropy/witness_entropy_quick.sh '$(GLOB)' '$(LIMIT)'
	@echo "CSV → analysis/entropy/witness_quick.csv"
