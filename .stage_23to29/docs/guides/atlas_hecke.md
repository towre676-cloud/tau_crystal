---
title: Atlas — Hecke data (breadth-first, Tier-A)
layout: page
permalink: /atlas/hecke
---

This page tracks the breadth-first **Tier-A** dataset: exact point counts for a small canonical set of minimal elliptic curves, exact \(a_p\) on a fixed prime panel (odd primes \(\le 199\), skipping bad primes and \(p=2\)), Hasse checks, per-curve receipts, and a top-level `atlas_hecke.jsonl` summary. Everything is plain text and hashed into the same ledger; each curve has a small **witness pack** you can verify offline with the sealed `tau_verify` binary. Parity/root numbers and high-precision \(L\)-data are reserved for Tier-B (non-gating) confirmations in a future PR; Tier-A remains zero-dependency and reproducible on a train with no Wi-Fi.

Key files:
- `scripts/atlas/curves_canonical.tsv` — the canonical curve list (extend by appending).
- `analysis/atlas/<label>/ap.tsv` — prime panel with exact \(a_p\).
- `analysis/atlas/<label>/leaf.json` — per-curve receipt (invariants, checks).
- `analysis/atlas/atlas_hecke.jsonl` — one-line JSON per curve (grep-able).
- `.tau_ledger/discovery/witness-*.tar.gz` — per-curve witness packs (text only).

To add a curve (minimal model), run:

`bash scripts/atlas/add_curve.sh N label a1 a2 a3 a4 a6` then `bash scripts/atlas/build_atlas.sh`.


## Example Usage

List rows with prime counts:
jq -r '.label + " (N=" + (.conductor|tostring) + "): " + (.panel.primes_evaluated|tostring) + " primes"' analysis/atlas/atlas_hecke.jsonl

python
Copy code

Find curves with any Hasse issues:
jq -r 'select(.flags.hasse_ok==false) | .label + " (worst r=" + (.checks.hasse.max_ratio|tostring) + " at p=" + (.checks.hasse.worst_p|tostring) + ")"' analysis/atlas/atlas_hecke.jsonl

css
Copy code

Filter parity-eligible central zeros (Tier-A heuristic):
jq -r 'select(.flags.candidate_central_zero==true) | .label' analysis/atlas/atlas_hecke.jsonl

bash
Copy code
