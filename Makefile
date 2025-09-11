SHELL := /bin/bash
diag: ; scripts/diag_crash.sh
assure:
	scripts/assure.sh
# tau make
.PHONY: serve call gate smoke ci-fixture
serve:
\tbash scripts/serve_fifo.sh &
call:
\tbash scripts/tau_llm_adapter.sh llm:proposer fixtures/contracts/example.contract.json out/llm.json
gate:
\tbash scripts/tau_gate.sh --verbose out/llm.json
smoke:
\tbash scripts/smoke.sh
ci-fixture:
\tTAU_LLM_CMD=$${TAU_LLM_CMD:-cat} bash scripts/tau_llm_adapter.sh llm:proposer fixtures/contracts/example.contract.json out/ci.llm.json && bash scripts/tau_gate.sh --verbose out/ci.llm.json

# --- repo-root fast path (added by setup) ---
.PHONY: ci-fast
ci-fast:
	@echo "[fast] repo-root: $$PWD"
	@# run spec-guard as a cheap invariant
	@[ -x scripts/spec_guard.sh ] && bash scripts/spec_guard.sh || echo "[skip] no spec_guard"
	@# OPTIONAL: add tiny smoke checks here (format/lint on staged subset, etc.)
