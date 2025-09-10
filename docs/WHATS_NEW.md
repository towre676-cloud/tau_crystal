# What’s new

τ-Crystal now ships a production-grade verification pipeline for discrete-symmetry claims in neutrino physics.

## Highlights

- **Cross-platform GAP gate** — Automorphism-order checks run via native GAP when available, else Docker/Podman, else fail loudly with a clear hint. No silent skips.
- **TM sum-rule pre-gates** — Before any diagonalization, we verify feasibility for:
  - TM1: `cos(theta12) * cos(theta13) = sqrt(2/3)`
  - TM2: `sin(theta12) * cos(theta13) = 1/sqrt(3)`
  This separates mathematical impossibility from physical implausibility.
- **Campaign grid & publishing** — Pre-committed contracts sweep `(template, theta13, beta)`. Receipts are frozen with dual SHA-256 hashes, and each campaign emits both a human-readable monograph and a machine `summary.json`.
- **Anti–Texas-Sharpshooter by construction** — Inputs, bounds, and witnesses are fixed before runs; receipts make any later goalpost-moving mechanically evident.

See `campaigns/<latest>/README.md` and `docs/monographs/residuals_YYYYMMDD.md` for the current falsification map.

## Method (contracts first, results second)

Each contract fixes:
1. the symmetry template `(Ge, Gnu, X)` or TM class,
2. numerical windows (e.g., `theta12 ∈ [20°,40°]`, `theta13 ∈ [5°,12°]`, `theta23 ∈ [35°,55°]`, `|delta| ≤ 10°`),
3. witnesses to record (preserved-column tests, mu–tau modulus equality, group orders).

A run produces a JSON receipt with `input_sha256` (contract) and `request_sha256` (dispatch). Green receipts confirm structural gates (e.g., Δ(27) basics, CP-unitary sanity); red receipts document falsifications against the pre-committed windows without parameter massage.

## Tiny tanh note

To keep parameters inside fixed physics windows without clamping artifacts, τ-Crystal uses monotone hyperbolic maps. For any real `u` and window `[a,b]`,

```
theta(u) = a + (b - a)/2 * (1 + tanh(u))
```

lands smoothly and deterministically in `[a,b]`. This is the same hyperbolic family that underlies familiar soliton profiles (`sech^2`) and domain-wall transitions; it gives smooth envelopes for sampling schedules and stable, invertible squashes for angles.

## One-screen quick start

Run sum-rule feasibility without diagonalization:
```bash
bash scripts/tau_exec.sh request.tm1_sumrule.json > analysis/tm1_sumrule.receipt.json
bash scripts/tau_exec.sh request.tm2_sumrule.json > analysis/tm2_sumrule.receipt.json
```

Run a residual-symmetry contract and produce a frozen receipt:

```bash
bash scripts/tau_exec.sh request.cp_residual_symm.tm1.json > analysis/cp_residual_symm.tm1.receipt.json
```

Publish a campaign folder with summary and monograph (outputs already wired in the repo):

```bash
camp="$(ls -d campaigns/residuals_*Z 2>/dev/null | tail -n1)"
sed -n '1,60p' "$camp/README.md"
```

## Short results (release blurb)

Under fixed windows `theta12 ∈ [20°,40°]`, `theta13 ∈ [5°,12°]`, `theta23 ∈ [35°,55°]`, `|delta| ≤ 10°`, we executed a grid over TM1, TM2, and mu–tau residual templates. TM sum-rules were feasible (`theta12 ≈ 34–36°` given `theta13 ≈ 9°`), but full residual witnesses failed systematically, especially in `theta23` and mu–tau modulus equality. Structural gates (Δ(27) basics, CP-unitary sanity, fermion mass-ratio checks) passed. Receipts are immutable and tagged for citation.

## GAP shim

`scripts/bin/gap` prefers a native `gap`; if absent it attempts `docker` then `podman`. If none are present, it exits with:

```
[gap-shim] no GAP engine found (native/docker/podman). Install GAP or Docker/Podman and retry.
```

This makes the automorphism-order gate predictable on every platform.
