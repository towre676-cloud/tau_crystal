Here’s the clean mapping from the Definitive HEO Architecture you just locked in to your two house frameworks:

How HEO slots into Freed–Steel (conceptual spine)

Think of Freed–Steel as your “math OS” with eight pillars (objects, operators, densities, residues, sheaves, flows, categorical glue, and verification semantics). Each HEO tier lands on one or more pillars:

Tier 0 — Axioms (upper density) → Density pillar.
HEO is the upper natural density of d‑power hits. This is the primitive observable every other layer refines.

Tier 1 — Operator algebra (Følner trace of a projection) → Operator pillar + Index semantics.

𝐷^𝑑 𝑘 is a diagonal projection; 𝐻𝑑𝑆(𝑘) is its per‑volume trace. “Finite surgery invariance” and “thinning bounds” are Freed–Steel invariants/monotones.

Tier 2 — Dirichlet series / residue → Residue pillar.
When a meromorphic continuation exists, the coefficient of the pole at 𝑠=1 matches the density. This is the precise “residue = effectiveness” bridge.

Tier 3 — 𝐹1 site / ghost divisors → Sheaf/stack pillar.
Packaging the hit set as a ghost divisor and defining deg(𝐷)=𝐻𝑑𝑆(𝑘) installs HEO as a degree functional on your arithmetic site.

Tier 4 — 𝑝‑adic densities / FF slope → Local–global and perfectoid pillar.

𝐻𝑑,𝑝𝑆(𝑘) is the local invariant; (where defined) the FF‑slope presents a geometric avatar. These are the “local receipts” that refine the global one.
Tier 5 — Pressure/KMS → Flow/thermo pillar.
Exact formula 𝑃(𝛽)=log(1−𝐻+𝐻e^𝛽) makes HEO the parameter of the Gibbs/KMS picture. It gives thermodynamic checks that are purely combinatorial.

Tiers 6–7 — Motivic/Hodge (clearly marked conjectural) → Deep geometry pillar (guard‑railed).
These provide typed Conjecture slots (not claims) that your spine knows how to carry without polluting the core invariants.

Tier 8 — Brocard → Concrete arithmetic case study.
Instantiates the core theorems (“finite → zero HEO”) and supplies regression tests.

Tier 9 — Periodic → Exact models pillar.
Rationality and cyclic-module structure give algebraic baselines and golden tests.

Tiers 10–11 — Higher category / Spectral action → Glue + physics interface pillars.
Lax functoriality expresses stability under thinnings/finite edits; spectral action ties the projection observable to a computable term in a trace functional.

How HEO integrates into τ‑Crystal (evidence, receipts, CI)

τ‑Crystal is your verification layer: everything is a typed claim with evidence and a receipt. HEO’s artifacts map cleanly:
Claim types you now have

Definition: 𝐻𝑑𝑆(𝑘); 𝐻𝑑,𝑝𝑆(𝑘); deg(𝐷𝑆,𝑘(𝑑)); 𝑃(𝛽).

Theorem: Finite‑solution filtering; finite‑surgery invariance; thinning bound; periodic rationality; residue‑equals‑density (under stated hypothesis).

Conjecture (guard‑railed): motivic/Hodge; FF‑slope equalities; spectral‑action coupling; arithmetic rigidity.

Each claim gets a receipt with:

type: Definition | Theorem | Conjecture

statement: the boxed equation/text verbatim from docs/specs/heo_universal_structure.md

assumptions: explicit (empty for pure defs)

evidence: proof sketch or pointer to computational checks

verif: scripts/tests that pass/fail deterministically
What CI should check (deterministic “green bars”)

Axioms & invariants

Evaluate (1/N) ∑_{n≤N} X_S(n) on test sequences (periodic, polynomial, factorial) and assert the limsup bounds/invariance under finite surgery and simple thinnings.

Periodic rationality

For random periods 𝑇 and random 0/1 patterns, check 𝐻 = (1/𝑇) ∑_{n≤𝑇} X(n) exactly.

Zeta side (when applicable)

For periodic X_S: compute ζ_S(s)=∑ a_n n^{−s} with a_n periodic; verify residue at s=1 equals the rational average.

Thermo side

Compute Z_N(β)=#0 + e^β #1 and verify P(β) matches log(1−H+H e^β) up to o(1).

𝑝‑adic side (local receipts)

For sample S (linear/polynomial), count A_{n,𝑝} via Hensel lifting; assert monotone upper bounds and record empirical limsup.

Brocard regression

Confirm the three known solutions are hit; assert the finite‑implies‑zero HEO theorem in the harness (conditional toggle).
Provenance + attestation you can attach

Spec: docs/specs/heo_universal_structure.md (canonical statements)

Equations spine: docs/specs/steel_equations.md (boxes that the CI parses)

Receipts: machine‑readable JSON per claim (stored under receipts/heo/...)

Runs: CI job artifacts (density traces, pressure curves, local 𝑝‑adic counts)

Working vocabulary (to keep everyone aligned)

HEO (global) is the Følner trace of a diagonal projection; it’s your density observable.

Local HEO 𝐻𝑑,𝑝𝑆(𝑘) is the limsup density of d‑powers mod 𝑝^𝑛; it’s your local receipt.

Degree receipt wraps 𝐻 as deg(𝐷) on the arithmetic site—useful when you want divisor calculus or torsion checks.

Thermo receipt is P(β) and yields closed‑form comparisons from first principles without analytic continuation.

Residue receipt applies only when analytic continuation is available; CI keeps it optional and never blocks on it.
What this buys you (practically)

A single invariant (𝐻) that is simultaneously:

measurable in finite time (via prefixes and limsup bounds),

stable under your allowed edits (finite surgery, thinnings),

bridgeable to analytic, arithmetic, and thermodynamic semantics,

and packaged as receipts your τ‑Crystal ledger can certify.

A clear separation: Tiers 0–5 feed hard, unconditional checks (great for CI); Tiers 6–11 are typed conjectural lanes that can live in the repo without contaminating proofs.

If you want, I can sketch the exact JSON schemas for the receipts and the minimal CI harness (CLI invocations and expected outputs) matching each theorem/definition above—so your Actions panel shows green for Tier‑0..5 on every push, and amber (skipped/optional) for the conjectural tiers.
