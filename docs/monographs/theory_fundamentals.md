# The Mathematical Architecture of τ‑Crystal

This monograph frames τ‑Crystal as a proof‑carrying runtime system for computational trajectories rather than endpoints. It formalizes the foliation of execution state space, the spectral τ‑sequence as a delay‑embedding, categorical receipt composition, and the Merkle‑DAG ledger as a cryptographic compression of computational context. The goal is a cohomologically constrained runtime epistemology with reproducible, CI‑ready receipts.

## Core mathematical spine
1. Trajectory foliation and invariant receipts.
2. Chebyshev τ‑sequence as spectral signature and attractor probe.
3. Categorical composition of receipts with traced monoidal flavor.
4. Merkle‑rooted chain as content‑addressed computational history.

## New diagnostic: τ‑Attractor Dimension and CEP
We introduce a τ‑Attractor Dimension estimate, \`dim_τ\`, derived from the scaling behavior of τ‑sequence increments, and a Chebyshev Entropy Profile \`CEP_τ\` summarizing multi‑scale dispersion. Both are byte‑stable JSON values emitted into `.tau_ledger/metrics/` and referenced by the manifest.

## Categorical receipt layer
Receipts compose as morphisms between canonicalized contexts. We expose a Lean scaffold `ReceiptCategory` and plan the instance `Obj := ReceiptContext`, `Hom := CanonicalReceipt`.

## Implications
This raises verification to the path level with spectral, categorical, and cryptographic invariants that survive environment changes while remaining CI‑practical.
