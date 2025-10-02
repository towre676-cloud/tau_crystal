# Lean 4 Formalization Notes (HEO)

- Project root: `lean/HEO`
- Build: `lake build` (CI calls `ci/heo/scripts/lean_ci.sh`)
- Main library: `HEO/Core.lean`
  - `X` — indicator for d-th power hits
  - `partialSum`, `density`, `H` — limsup density
  - Statements: `finite_implies_zero`, `finite_surgery_invariance`, `periodic_rationality`
- Current status: includes `sorry` placeholders; workflow is **non-blocking**.
- Next steps:
  1. Replace `sorry` in `density_bounds` proof case-split with a lemma `X∈{0,1}`.
  2. Prove `finite_implies_zero` via `partialSum ≤ C` ⇒ density → 0 ⇒ limsup = 0.
  3. Prove `finite_surgery_invariance` by bounding prefix differences.
  4. Periodic rationality: show Cesàro limit equals period average.

Pin mathlib commit for reproducibility once proofs stabilize.
