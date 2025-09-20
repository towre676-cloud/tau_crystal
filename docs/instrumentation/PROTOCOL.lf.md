# Pre-Registered Protocol (Decisive Test)

We test: **Can a facial-geometry pipeline, after canonicalization and rational reconstruction,
yield standard elliptic curves whose coefficients pass integrality, multiplicativity,
Ramanujan, and stability?** If not, the claim is withdrawn.

## Decision Rule
For 50 subjects (3 sessions each), require:
- Survival ≥ 40 curves after canonical → \(E/\mathbb{Q}\) construction checks
- For each surviving subject: pass **T1–T4**
  - T1 Integrality: all \(a_p \in \mathbb{Z}\) for \(p \le 10^4\)
  - T2 Multiplicativity: \(a_{mn}=a_ma_n\) for \((m,n)=1\), \(m,n \le 400\)
  - T3 Ramanujan: \(|a_p| \le 2\sqrt{p}\) for good \(p \le 10^4\)
  - T4 Stability: \(a_p^{(sess2)}=a_p^{(sess3)}\) for \(p \le 10^3\)

**Any single failure ⇒ accept \(H_0\)** (instrument does *not* meet arithmetic discipline).
Otherwise reject \(H_0\) and publish curves + coefficients for audit (no new math claimed).

## Inputs / Outputs
Inputs (public):
- `schemas/rational_invariants.csv` (per subject/session: 17 rationals)
- `analysis/arith/canonical_cr_indices.txt` (fixed 4‑tuple list; hashed)
- `analysis/arith/j_coeffs_Z.txt` (fixed integer coefficients for j‑map; hashed)

Outputs (public):
- `analysis/arith/coefficients.csv` (subject,session,prime,ap,N,good_bad,local_type)
- `analysis/arith/an_table_upto_400.csv` (subject,n,an)
- `analysis/arith/stability_test.csv` (subject,prime,ap_sess2,ap_sess3,delta)
- `analysis/arith/report.json` (pass/fail per test + SHA256 of all inputs)

## Reproducibility
- Docker image pins Sage/Pari/Rust versions
- Single `Makefile` target runs end-to-end
- Signed git tag and SHA-anchored protocol file ensure immutability

**Scope:** This measures distributions on \(\mathcal{M}_{1,1}(\mathbb{Q})\).  
It does **not** claim new \(L\)-functions or new Langlands correspondences.
