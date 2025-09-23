# τ‑Crystal Langlands Laboratory: Second Witness, Reciprocity, and Critical‑Zero Diagnostics

This record consolidates the present state of the bash‑native automorphic laboratory inside τ‑Crystal. It documents the reciprocity pipeline with fixed‑point arithmetic, the emergence of a second reciprocity witness, the double‑zero detection and refinement subsystem, and the arithmetic plumbing that supports these constructions. Everything described here is live and reproducible in this repository using only portable shell and standard utilities, with artifacts traceable through the ledger and, where configured, CI.

## Abstract

The laboratory operationalizes a correspondence by matching a Hecke‑smoothed mean on one side to a θ‑transformed mean on the other, over a grid in slope–intercept micro‑units. The search produces deterministic receipts, a frozen “best” witness, and a resilient fallback for downstream tools. A companion apparatus scans JSON receipts for critical ordinates, clusters them in micro‑space, and refines candidates into a compact visual strip. Arithmetic infrastructure provides base‑10 fixed‑point conversion, integer square root, bounded normalization, and micro‑safe transforms that behave consistently across platforms, including Windows Git Bash.

## Verified State

A second reciprocity witness has been persisted under analysis as environment and text summaries. The fallback helper emits frozen S/T pairs when present, allowing downstream tools to remain parameterized while scans regenerate. The double‑zero tools write TSV ledgers and SVG strips directly from repository receipts. All arithmetic is encoded in integer micro‑units to guarantee determinism.

## Arithmetic Plumbing

Fixed‑point base‑ten micro arithmetic avoids locale and octal hazards and supports integer square root for Hecke‑style smoothing. Clamping keeps transforms within the lattice, ensuring reproducible outputs across shells and operating systems.

## Minimal τ Operations and Reciprocity

Extraction maps receipts to micro‑normalized streams. Hecke smoothing suppresses spikes while preserving coarse structure; a θ‑affine step applies slope and intercept in micro units and clamps results. A grid search over (S,T) records absolute micro deltas of A/B means, freezes the best pair for reuse, and verifies tolerance on demand for deterministic re‑attestation.

## Second Witness

Multiple reciprocity witnesses are now present, including a second persisted pair. Their coexistence indicates a structured locus of agreement rather than an isolated coincidence and motivates finer micro grids, adaptive descent, and alternate smoothing schedules.

## Double‑Zero Diagnostics

A scanner aggregates critical ordinates from JSON, converts to micro units, clusters within an ε‑band, and records centers, spans, and membership. A refiner revisits each neighborhood with tighter radii and renders a strip visualization in SVG with categorical marks for solitary and clustered knots.

## Portability and Reproducibility

Scripts avoid process substitution in hot paths, disable history expansion, and rely on ubiquitous text utilities. Outputs are plain text and SVG, stable under repeated runs, and suitable for ledger inclusion and CI publication.

## Outlook

The presence of multiple witnesses and persistent critical‑zero structure suggests mapping a parameter atlas with Morse‑style classification of Δ terrain, p‑adic weight drifts, and stricter spectral checks, while enriching the ledger with structured run contexts and functional‑equation probes.
