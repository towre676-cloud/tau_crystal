# τ-Crystal — One-Stop HOWTO

This page aggregates every entrypoint and integration pattern for humans, CI, and LLM agents.

## 1) Start the FIFO transport
```bash
cd ~/Desktop/tau_crystal/tau_crystal
bash scripts/serve_fifo.sh &
```

## 2) Send a request (three ways)
```bash
# stdin
printf "%s" '{"tool":"llm:proposer","input_path":"fixtures/contracts/example.contract.json","output_path":"out/resp.json"}' | bash scripts/tau_pipe.sh
# file
bash scripts/tau_call_file.sh fixtures/requests/proposer.req.json
# positional (if you have scripts/tau_call.sh)
bash scripts/tau_call.sh llm:proposer fixtures/contracts/example.contract.json out/resp2.json
```

## 3) Optional HTTP bridge (localhost only)
```bash
# socat
bash scripts/http_bridge_socat.sh &
# test
curl -s -X POST http://127.0.0.1:8787/tau/step \\
  -H "Content-Type: application/json" \\
  -d '{"tool":"llm:proposer","input_path":"fixtures/contracts/example.contract.json","output_path":"out/bridge.json"}'
```

## 4) LLM adapter (semantic + behavioral verification)
```bash
# optional: provide a local LLM CLI (stdin→stdout)
export TAU_LLM_CMD="ollama run llama3"   # example
# optional: provide an embedder CLI for cosine embeddings
export TAU_EMBED_CMD="ollama run nomic-embed-text"
bash scripts/tau_llm_adapter.sh llm:proposer fixtures/contracts/example.contract.json out/llm.json
```
Output includes:
- `semantic`: cosine_bow, jaccard_2gram, and optional cosine_embed.
- `behavior.consistency`: invariant paraphrase checks with `consistency_rate`.
- `behavior.constraints`: required-key validation, adversarial probes.

## 5) CI usage & semantic gate
Set in your workflow/job env when you want strict gating:
```bash
TAU_SEMANTIC_GATE=1
TAU_SEM_EMBED_MIN=0.85   # default
TAU_SEM_BOW_MIN=0.75     # default
```
If no `TAU_LLM_CMD` is configured on CI, the gate uses `cosine_bow` only.

## 6) Tuning & env knobs
- `TAU_EXPECT_KEYS` (csv): required keys for constraint checks (default: `output_text`).
- `TAU_BEH_EMBED_MIN` / `TAU_BEH_BOW_MIN`: per-run thresholds for consistency testing.
- `TAU_TIMEOUT`: seconds to wait for FIFO replies.

## 7) Where things land
- Envelopes: `.tau_fifo/logs/*.json`
- LLM adapter artifacts: `out/*.json`
- Receipts/ledger (if enabled elsewhere): `.tau_ledger/*`

## 8) Gating & pre-commit
Gate any adapter JSON locally:
```bash
bash scripts/tau_gate.sh --verbose out/llm.json
```
Install pre-commit hook to gate staged `out/*.json`:
```bash
bash scripts/install_precommit_gate.sh
```
Env knobs (defaults in parens): `TAU_SEM_EMBED_MIN` (0.85), `TAU_SEM_BOW_MIN` (0.75), `TAU_CONSIST_MIN` (0.67), `TAU_REQUIRE_CONSTRAINTS` (1), `TAU_REQUIRE_ADVERSARIAL` (0).
Use `--strict` to set tighter gates (embed≥0.90 / bow≥0.80 / consist≥0.80 and require adversarial pass).

## 9) Quick smoke
```bash
# default: TAU_LLM_CMD=cat (echo stub)
bash scripts/smoke.sh
# strict mode (tighter gates):
TAU_STRICT=1 bash scripts/smoke.sh
# with your local LLM CLI:
TAU_LLM_CMD="ollama run llama3" bash scripts/smoke.sh
```
