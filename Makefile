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
.PHONY: report-progress
report-progress:
\t@printf '%s\n' 'Report → docs/progress/resurrection_progress_2025-09-29.md'
\t@printf '%s\n' 'Ledger → .tau_ledger/summary/resurrection_progress_2025-09-29.json'
\t@sed -n '1,60p' docs/progress/resurrection_progress_2025-09-29.md | sed 's/\r$//'
# === Freed alignment ===
.PHONY: freed-receipts freed-verify freed-open
freed-receipts:
\t@bash scripts/freed/generate_receipts.sh
freed-verify:
\t@bash scripts/freed/verify_pullbacks.sh
freed-open:
\t@printf "%s\n" "docs/freed/alignment_table.md" "docs/freed/relative_tft_functor.md" "docs/freed/anomaly_line_trivialization.md" "docs/freed/tmf_sigma_orientation.md"
# === Freed alignment (proof+meas) ===
.PHONY: freed-phi freed-tmf freed-proof freed-open2
freed-phi:
\t@bash scripts/freed/run_phi_checks.sh
freed-tmf:
\t@bash scripts/freed/run_tmf_sigma.sh
freed-proof:
\t@printf "%s\n" "Lean capsules at TauCrystal/Freed/*.lean (compile wiring TBD)"; exit 0
freed-open2:
\t@printf "%s\n" "docs/freed/relative_tft_functor.md" "docs/freed/anomaly_line_trivialization.md" "docs/freed/tmf_sigma_orientation.md"
# === Freed live runners ===
.PHONY: freed-receipts-list freed-lean
freed-receipts-list:
\t@ls -1 .tau_ledger/freed 2>/dev/null || true
freed-lean:
\t@lake build || true
