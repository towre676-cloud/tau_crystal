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

