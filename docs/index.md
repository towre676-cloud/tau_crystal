# τ‑Crystal Adapter — Quickstart & API

[![Adapter CI](https://github.com/towre676-cloud/tau_crystal/actions/workflows/adapter-ci.yml/badge.svg)](https://github.com/towre676-cloud/tau_crystal/actions/workflows/adapter-ci.yml)

This site mirrors the essential entrypoints for LLMs, agents, and humans. The canonical transport is **FIFO-based**, Bash-only. HTTP specs below are for teams that must bridge to REST but are not required for local usage.

## Zero‑Config Local Use
```bash
cd ~/Desktop/tau_crystal/tau_crystal
bash scripts/serve_fifo.sh &                               # start the transport
printf "%s" '{"tool":"llm:proposer","input_path":"fixtures/contracts/example.contract.json","output_path":"out/resp.json"}' | bash scripts/tau_pipe.sh
cat out/resp.json
```

## Schemas & Specs
- Request schema: [`schema/request.schema.json`](../schema/request.schema.json)
- Response schema: [`schema/response.schema.json`](../schema/response.schema.json)
- OpenAPI (spec only): [`api/openapi.yaml`](../api/openapi.yaml)
- JSON‑RPC schema: [`api/jsonrpc.schema.json`](../api/jsonrpc.schema.json)
- JSON‑RPC example: [`api/jsonrpc.example.json`](../api/jsonrpc.example.json)

## Philosophy
The adapter is a **universal actuator** for LLMs: JSON in, JSON out, fully local, auditable, and hash‑stable. If you need HTTP, point a tiny bridge at the same contract; the FIFO transport remains the source of truth.
