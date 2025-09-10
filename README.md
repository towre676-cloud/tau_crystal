# τ‑Crystal
[![Adapter CI](https://github.com/towre676-cloud/tau_crystal/actions/workflows/adapter-ci.yml/badge.svg)](https://github.com/towre676-cloud/tau_crystal/actions/workflows/adapter-ci.yml)

Local, composable, verifiable symbolic transport system for agent-safe computation. Shell-first, LLM-aligned, and cryptographically rooted.

## Key Entrypoints
- [`doc/tau_llm_adapter.md`](doc/tau_llm_adapter.md) – full adapter protocol for LLMs, CLI, CI
- [`fixtures/`](fixtures/) – minimal contracts + requests to test adapter calls
- [`schema/`](schema/) – JSON schema for request and response format
- [`scripts/`](scripts/) – adapter transport logic (callers, server, receipts)

## Minimal Example
```bash
cd ~/Desktop/tau_crystal/tau_crystal
bash scripts/serve_fifo.sh &
bash scripts/tau_call_file.sh fixtures/requests/proposer.req.json
cat out/fixture.proposal.json
```

To route any prompt or agent call into the adapter, emit a request like:
```json
{
  "tool": "llm:proposer",
  "input_path": "fixtures/contracts/example.contract.json",
  "output_path": "out/proposal.json"
}
```

Then call via:
```bash
cat request.json | bash scripts/tau_pipe.sh
```

The entire stack is pure Bash. Zero dependencies. FIFO‑only. Ready for LLMs, CI, and shell orchestration.

## Documentation
- GitHub Pages: See `/docs` site (published automatically by CI).
- Full adapter monograph: [`doc/tau_llm_adapter.md`](doc/tau_llm_adapter.md)

## Build Receipts
[![Lake Receipts](https://github.com/towre676-cloud/tau_crystal/actions/workflows/lake-receipts.yml/badge.svg)](https://github.com/towre676-cloud/tau_crystal/actions/workflows/lake-receipts.yml)
If this repo includes a Lean/Lake project, CI will publish chained receipts under `.tau_ledger/` for every build.

## HOWTO
- See the one-stop guide: [`doc/HOWTO.md`](doc/HOWTO.md)

## What’s new in τ-Crystal
- See docs/WHATS_NEW.md for details of the verification pipeline, TM pre-gates, and campaign publishing.
- For auditors: docs/REPRO.md is a one-page, bash-only rerun and hash verification guide.
