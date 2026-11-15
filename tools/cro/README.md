# Crystalline Residue Object
## Historical recovery and a certified finite descent model

### Replay

Python 3.10+ verifies receipts with its standard library. Generation was tested with SymPy 1.14.0. The Lean witness file uses Std only.

```bash
python -S cro.py verify fixtures/sheared-monodromy.input.json fixtures/sheared-monodromy.receipt.json
python cro.py make fixtures/sheared-monodromy.input.json
python -m unittest -v
lean +leanprover/lean4:v4.20.0 CROWitness.lean
```

The input digest binds sorted compact JSON containing the full integer matrices, explicit C⁰ dimension and residue. All arithmetic is exact. A receipt carries either a failed cocycle equation, a correction, a rational separating functional, or an exact torsion order with upper and lower witnesses. The verifier checks these equations directly and never runs Smith reduction. The digest binds an input to its receipt but carries no authorship or execution signature.

### Original content and its evidence

| Date (UTC) | Evidence and finding |
|---|---|
| 2025-08-31 03:59:27 | Recovered user-authored discussion named nilpotent thickenings, divided powers, flat connection, Frobenius and obstruction cohomology. An exact site, coefficient ring and covers remain unspecified in the retrieved fragments. |
| 2025-08-31 04:01:37 | Recovered assistant sketch for `CrystallineResidue.lean` proposed a `residueNorm` that returned the constant norm of β, and a `ResidueDescentTheorem` about H¹. This does not supply a norm on a cohomology class or prove the equivalence. |
| 2025-08-31 04:12:45 | Recovered assistant sketch for `CrystallineTrace.lean` used Φ = βI + γP, γ = n(α−β), with P a rank-one projector. It proposed an equality between a probe and the normalized trace. See the corrected condition below. |
| 2025-09-03 | [Tracked qCRO emitter](https://github.com/towre676-cloud/tau_crystal/blob/a9a41cebb809b8dea9c8a9720943d28bbc4d0a7f/tools/QCRO.lean) emits an input obstruction value multiplied by 1 + q·edges + q²·faces. [The later adapter](https://github.com/towre676-cloud/tau_crystal/blob/8729185784546bfd1edeecd85f66086f6af28ba0/py_ledger/qcro_adapter.py) attaches existing samples to τ indices. Neither computes cohomology. The early [Core.Sheaf](https://github.com/towre676-cloud/tau_crystal/blob/a9a41cebb809b8dea9c8a9720943d28bbc4d0a7f/Core/Sheaf.lean) gives a trivial propositional gluing predicate. |
| 2025-09-13 | [Tracked τ-sheaf reflection script](https://github.com/towre676-cloud/tau_crystal/blob/dc4bf2f418cd0ed130a43a97391c964481a0d486/scripts/meta/tau_sheaf_reflect.sh) computes a rolling hash of ledger records. |
| 2025-09-20 | [Tracked cohomology tagging script](https://github.com/towre676-cloud/tau_crystal/blob/4bd6380d3e2b578dccf8acf7ba3391589daffc07/scripts/coho/fix_and_tag.sh) can synthesize runs if missing and labels a sector by a digest byte modulo seven. This label does not implement semilinear Frobenius. |
| 2025-09-23 22:04:02 | Recovered user-authored note links a time-window τ-sheaf to the differential residual R = u′−F(u), overlap defects, transport I + Δt·DF + εS, q-traces and receipts. This is the strongest recovered source for the model developed here. |
| 2025-09-29 UTC | [Tracked Volume II scaffold](https://github.com/towre676-cloud/tau_crystal/blob/3c3c954191089e4aced9b672cc44b00bf28567b2/src/TauCrystal/TauSheaf.lean) pairs a generic sheaf with convergence metadata. [Its companion note](https://github.com/towre676-cloud/tau_crystal/blob/3c3c954191089e4aced9b672cc44b00bf28567b2/doc/monographs/volume2_descent_spectrum.md) describes capsule import chains and receipts. |

The conversation findings come from recovered dated summaries without stable original chat links. The Git entries are direct source inspection at pinned revisions.

### Theorem · finite integral descent with exact-order certificates

Let D₀ and D₁ define a finite free integral cochain complex in degrees 0, 1, 2. For an edge residue r, the following cases are exhaustive and exclusive.

1. **Non-cocycle.** D₁r ≠ 0. A row and its nonzero value certify this.
2. **Gluing.** D₁r = 0 and D₀x = r for some integer x. For a torsor, subtract x from the chosen local sections.
3. **Infinite order.** D₁r = 0 and an integer functional λ satisfies λD₀ = 0 and λr ≠ 0. This also proves nonvanishing over ℚ.
4. **Finite order h > 1.** D₁r = 0, an integer x satisfies D₀x = hr, and a collection of integer functionals λᵢ satisfies λᵢD₀ ≡ 0 mod mᵢ. Require
   `lcm_i(m_i / gcd(m_i, λ_i r)) = h`.

**Proof.** All four receipts are sound by substitution. In the fourth case, any multiplier k with k[r]=0 must annihilate λᵢr in ℤ/mᵢ for each i. The additive order there is mᵢ/gcd(mᵢ,λᵢr). The least common multiple divides every such k and the displayed lift shows h itself works. For completeness, take a Smith decomposition U D₀ V = D and let b = Ur. If b has a nonzero coordinate in a zero row of D, the corresponding row of U separates over ℚ. Otherwise the equations D y = kb hold exactly when every nonzero diagonal entry dᵢ divides kbᵢ. Their least positive common multiplier is the lcm of |dᵢ|/gcd(dᵢ,bᵢ). The corresponding rows of U give the modular witnesses. The correction is V y. If that multiplier is 1 the class vanishes. This proof identifies the order of the specific class. It does not assert that other classes vanish.

The verifier rejects input with D₁D₀ ≠ 0 before interpreting r. The finite theorem uses standard Smith normal form. See [Smith normal form lecture notes](https://bpb-us-w2.wpmucdn.com/sites.udel.edu/dist/3/7714/files/2022/03/845f15LecsProblemsDec032015.pdf) and [Stacks Project, First cohomology and torsors](https://stacks.math.columbia.edu/tag/03AG).

### Worked case · obstruction missed by rational and prime-field checks

For a circle with lattice ℤ² and monodromy M = [[1,4],[0,1]], the cellular complex has D₀ = M−I and D₁ = 0. The residue (2,0) has exact order two. Over ℚ one takes x₂=1/2. Modulo two the residue itself vanishes. Over any odd prime field 4 is a unit. Yet no integral correction exists. Modulo four, projection to the first coordinate kills the image of D₀ and sends the residue to two. Doubling the residue admits the explicit lift (0,1). This example is exported with its receipt.

### From the time-window notes to computable overlap data

For an approximate trajectory u of a smooth ODE u′ = F(u), the local differential residual is b(t) = u′(t)−F(u(t)). Let T(t,s) be exact propagator transport for the linearized correction equation. Its inhomogeneous contribution on a window is

```text
B(t,s) = integral_s^t T(t,v) b(v) dv
B(t,s) = B(t,m) + T(t,m) B(m,s).
```

The second identity follows by splitting the integral and composing the exact propagator. It gives a diagnostic for window refinement and sign conventions. The assembled integral problem further requires a specified lattice preserved by the comparison maps and a lattice-valued overlap residual. Arbitrary floating-point ODE data do not have this property.

For the finite simplicial model, choose invertible transports Tᵢⱼ with Tᵢₖ = Tⱼₖ Tᵢⱼ on each face. Use (D₀a)ᵢⱼ = aⱼ−Tᵢⱼaᵢ and (D₁r)ᵢⱼₖ = rⱼₖ−rᵢₖ+Tⱼₖrᵢⱼ. Expanding the composite yields (Tᵢₖ−TⱼₖTᵢⱼ)aᵢ. Thus a violation of flatness shows up before a cohomology class can be assigned. The supplied assembler validates inverse matrices and checks the composite exactly. For a genuine cover with nontrivial restriction maps the nerve must retain the appropriate coefficient modules on intersections. The simplified assembler assumes fibers of one fixed rank and transport on edges.

### q deformation that preserves the complex

Choose scalar edge weights Tᵢⱼ = q^{wᵢⱼ} over ℤ[q,q⁻¹]. Impose wᵢₖ = wᵢⱼ + wⱼₖ on all faces. This yields an actual Laurent-polynomial cochain complex. On a circle with total winding weight k the cellular differential is q^k−1 under the convention D₀=M−I. For k≠0 the first cohomology is ℤ[q,q⁻¹]/(q^k−1). Over a field, specialize at a nonzero q₀ and the dimension jumps from 0 to 1 exactly when q₀^k=1. Over ℤ, q₀=−1 and odd k gives ℤ/2. The case k=0 yields the full coefficient module in degree 1. This q-family is a new construction. The implemented integer verifier checks specialized complexes and does not calculate polynomial Smith forms.

### Trace and crystalline scope

For a unit vector v and P=vvᵀ, tr(βI+γP) = nβ+γ, so γ=n(α−β) enforces tr Φ=nα. A unit probe r measures β+γ|rᵀv|². To identify its value with tr Φ/n when γ≠0, require |rᵀv|²=1/n. Choosing r=v fails for n>1. An exact alternative is to average over an orthonormal basis. Trace matching, overlap coherence and cohomological vanishing are separate tests.

A classical crystalline interpretation needs a site of divided-power thickenings and crystal comparison isomorphisms. A Frobenius structure needs a suitable base endomorphism and compatible pullback maps. At the cochain level, σ-semilinear maps Fₖ commuting with Dₖ send boundaries to boundaries and cocycles to cocycles, so they induce a well-defined action on the obstruction class. To claim an actual F-crystal one must supply and validate the underlying site, base-change and Frobenius data. The finite certificate does not construct them. See [Stacks Project, Crystals in modules](https://stacks.math.columbia.edu/tag/07IR).

### Verification scope

Six test methods replay the five checked fixtures, reject tampering and malformed complexes, exercise both a flat and a nonflat triangle, and compare 300 rectangular instances to known exact outcomes under unimodular basis changes. Lean kernel-checks the two separating-witness lemmas and the order-two arithmetic example. The general Smith completeness proof is given above in ordinary mathematics. The historical repository and deployed endpoints were used only as research evidence. This package is a staged candidate for review.

### Exact transport-to-receipt bridge

`transport.py` derives a cellular CRO complex from piecewise affine ODE data. A window of duration t solves x′ = Nx + b with constant integer N and b and N² = 0. Its exact map is

```text
A = I + tN          A⁻¹ = I − tN
c = tb + (t²/2)Nb   x_end = A x_start + c
```

The formula follows by differentiation with the correct initial value. Use rational durations and check that A, A⁻¹, and c have integer entries at each boundary. Thus each boundary map is an affine automorphism of the chosen standard lattice. This construction asserts lattice preservation at the listed boundaries. An additional subdivision is admissible exactly when its own boundary maps meet the integral checks.

Compose the windows in time order to obtain x ↦ Mx + c. A periodic integral trajectory exists if and only if (M−I)x = −c has an integer solution. More generally the correction class lies in coker(M−I), and its exact order is certified by the finite descent theorem. Changing the origin by a lattice vector a changes the translation by (M−I)a and preserves the class. The derivation and verifier both check local maps, their composition, the cycle digest, and the final witness. Verification uses only Python's standard library.

```bash
python transport.py make fixtures/periodic-ode.cycle.json
python -S transport.py verify fixtures/periodic-ode.cycle.json fixtures/periodic-ode.bundle.json
```

The two-window fixture is a new controlled benchmark inspired by the original time-window notes. It yields M = [[1,4],[0,1]] and c = (2,0) from the explicit ODE x₁′ = 4x₂ + 2, x₂′ = 0 over one period of length 1. The rational periodic initial value has x₂ = −1/2. No integral initial vector is periodic. Two copies of the additive forcing class admit a correction, and the modular witness certifies that one copy cannot. This is additive order in the cokernel, rather than a claim about traversing two periods of the original affine map. The code does not infer a lattice in the legacy sampled runs or construct a crystalline site.
