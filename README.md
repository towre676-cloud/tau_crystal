# τ‑Crystal

[![spec-guard](https://github.com/towre676-cloud/tau_crystal/actions/workflows/spec_guard.yml/badge.svg?branch=main)](https://github.com/towre676-cloud/tau_crystal/actions/workflows/spec_guard.yml)
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

## Canonical request ingress

Every run now begins by freezing the exact request bytes and emitting a single SHA-256 digest. The bytes are written verbatim to `analysis/<stem>.request.canon.json` by `scripts/bin/save_request_preimage.sh`; the digest is printed to stdout and, if you prefer, saved as a sidecar with `scripts/bin/bind_request.sh`. This seals the entrance: auditors can recompute the same hash on any machine and verify that the bytes cited by the ledger are the bytes that actually crossed the boundary. See `docs/monographs/request_preimage_canon.md` for the full rationale.

```bash
# stdin → canonical preimage + digest sidecar
printf "{\"tau\":1,\"q\":[0,0.5,1]}\n" | scripts/bin/bind_request.sh demo - > .tau_ledger/demo.sha256
# from file → same result; adapter unchanged
scripts/bin/bind_request.sh tm1 request.tm1_sumrule.json > .tau_ledger/tm1.sha256
```

### Ground-truth audit
A reproducible, host-agnostic audit of the current default branch—what τ-Crystal guarantees today, where those guarantees stop, and how the canonical request ingress fits the proof story—is available under `docs/audits/`. It is written to be replayed verbatim on any Unix host with elan installed.

## CI speed benchmarks (receipt-backed)
Warm runs on unchanged mathlib are materially faster than cold runs. We publish medians and a cold/warm factor from attested NDJSON lines and receipts; see `docs/benchmarks/ci_speed.md` for the current table and recent receipt hashes. Trigger the matrix via “CI Bench” (workflow_dispatch) and download the artifacts if you want to compare against your own fork.
