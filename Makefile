# === Entropy quick (env-driven) ===
# Usage example:
#   PATH_GLOB=./.tau_ledger/entropy/witness_*.json LIMIT=200 make entropy-quick
.PHONY: entropy-quick
entropy-quick:
	@sed -i 's/\r$$//' scripts/entropy/witness_entropy_quick.sh || true
	@PATH_GLOB="$(PATH_GLOB)" LIMIT="$(LIMIT)" bash scripts/entropy/witness_entropy_quick.sh
	@echo "CSV → analysis/entropy/witness_quick.csv"
# === Entropy report ===
# Use: N=30 make entropy-report   (default N=20)
N ?= 20
.PHONY: entropy-report
entropy-report:
	@sed -i 's/\r$$//' scripts/entropy/report_quick_top.sh || true
	@bash scripts/entropy/report_quick_top.sh "$(N)"
# === Entropy deep report ===
# Usage:
#   make entropy-report-deep
#   N=50 SORT_FIELD=H8_est make entropy-report-deep
N ?= 30
SORT_FIELD ?= cr_gz
.PHONY: entropy-report-deep
entropy-report-deep:
	@sed -i 's/\r$$//' scripts/entropy/report_deep_outliers.sh || true
	@bash scripts/entropy/report_deep_outliers.sh "$(N)" "$(SORT_FIELD)"
