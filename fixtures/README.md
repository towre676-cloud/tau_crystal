# Fixtures for τ‑Crystal Adapter

This directory contains minimal, reproducible practice files that any human, CI job, or LLM agent can use to exercise the τ‑Crystal adapter transport. Everything is filesystem‑local and Bash‑only.

## Contents
- `contracts/example.contract.json` – tiny demo contract
- `requests/proposer.req.json` – calls `llm:proposer`
- `requests/digest.req.json` – calls baseline digest

## One‑Minute Quickstart
```bash
cd ~/Desktop/tau_crystal/tau_crystal
bash scripts/serve_fifo.sh &                    # start transport
bash scripts/tau_validate.sh request fixtures/requests/proposer.req.json
bash scripts/tau_call_file.sh fixtures/requests/proposer.req.json
cat out/fixture.proposal.json                  # adapter output
```

## Log Template (paste into issues/PRs/notes)
```text
System: <OS + shell>
Commit: <git rev-parse --short HEAD>
Server start:
  $ bash scripts/serve_fifo.sh &
Request:
  $ bash scripts/tau_call_file.sh fixtures/requests/proposer.req.json
Response envelope:
  {"ok":true,"stdout":"..."}
Artifact:
  out/fixture.proposal.json (size: <bytes>, sha256: <hash>)
```

## Troubleshooting
- If nothing happens: ensure `scripts/serve_fifo.sh` is running.
- If timeout: increase `TAU_TIMEOUT` (e.g., `TAU_TIMEOUT=120`).
- If missing tools: confirm `scripts/*` are executable (`chmod +x`).
