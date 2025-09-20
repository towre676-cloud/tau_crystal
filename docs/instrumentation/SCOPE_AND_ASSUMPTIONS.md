# Scope, Assumptions, and Claim Boundary

**Scope.** This repository ships an auditable **instrument** that maps canonical 3-D landmarks
to classical elliptic curves and their arithmetic invariants with cryptographic provenance.
It does **not** claim that facial geometry is intrinsically arithmetic.

**Standing Claims (allowed):**
- Deterministic, receipt-bound pipeline from invariants → \(E/\mathbb{Q}\) → \((a_p,N,\dots)\)
- Reproducibility: third parties can recompute and verify signatures and counts
- Statistical *instrumentation* of distributions on \(\mathcal M_{1,1}(\mathbb Q)\)

**Non-Claims (forbidden until proven):**
- Any intrinsic “facial arithmetic” or new reciprocity
- Any “meaningful mapping” assertion beyond instrumentation
- Any causal link not supported by preregistered, replicated tests

**Meaningfulness Hypothesis.** The face→curve map is called *meaningful* only if **all**
M1–M8 (docs/instrumentation/MEANINGFULNESS.md) pass against explicit nulls (N0/N1),
with preregistration and an independent replication. Until then, **instrument-only**.
