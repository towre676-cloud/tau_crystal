# τ‑Crystal Activation Checklist (Descent • Invariants • Audit • Freed Cross‑Refs)

**Top‑Level Activation Map**
| Cluster | Artifact | Invariant | Descent Condition | Audit Hook | Freed Cross‑Ref |
|:--|:--|:--|:--|:--|:--|
| Morphic Echo | echo_chain.json; cone_homology.json | H•(Cone(U)) computed; Betti + graded ΔS | Cone sheafifies over τ‑subintervals | Merkle siblings for H_*; replay U | Segal bordism composition; factorization locality |
| Čech Curvature | cover_windows.json; glue_gij.json; cocycle_cijk.json | δg=c; δc=1; ℓ(c)∈ℕ; KL(μ_t‖μ_{−t}) | Identities persist under cover refinement | g‑paths and c exposed in verifier | Anomaly = obstruction to global section |
| Motive Embedding | variety_spec.json; period_values.json; receipt_binding.json | reg(R)=per(R); comp_{B,dR} (example) | Gal(ℚ(b)/ℚ) descent recorded | Variety spec + binding proof hash | Periods as QFT observables; index/regulator |
| Sealing / Integration | pushout_manifest.json; verifier_certificate.json | Terminal pushout; H_τ reproduced | Kan extension along 𝒟↪𝒞 | Full Merkle tree JSON | Bordism‑style gluing; factorization |

**Static Substrate (Freeze First)**
| Symbol | Meaning | Minimal Contents | Descent/Audit Extension |
|:--|:--|:--|:--|
| 𝒞 | Typed execution category with receipts | Objects S; morphisms f:S→S′ with ρ(f); π:𝒞→τ | Fibered in groupoids; simulations as 2‑cells |
| Σ | Typed signature algebra | Constructors; typing; assoc/identity | Sheaf descent for Σ‑terms; proof‑trace morphisms |
| 𝓟 | Provenance algebra | ℤ⟨receipt symbols⟩; boundary ∂ from grammar | ∂ natural w.r.t. pullbacks; homology exposed |
| Ch(𝓟) | dg‑category over 𝓟 | Complexes; chain maps; cones; H_* | Stackifies over 𝓛; H_* with Merkle siblings |
| 𝓛 | Site of τ‑intervals | Joyal–Tierney coverage | Effective epis; cover recomputation |
| G | Relabeling automorphism group | Generators/relations preserve type/order/hash | Compatible descent action; generator metrics |

**Execution Order (Hard Dependencies)**
| Step | Deliverable | Gating Proof/Check | Descent/Audit Add‑On |
|:--|:--|:--|:--|
| 1 | Freeze 𝒞, Σ, 𝓟(∂), 𝓛, Ch(𝓟) | Cone(id) acyclic; Σ laws | Fibration descent ok; type‑iso groupoid emitted |
| 2 | Morphic Echo prototype | Betti(Cone(U)); graded ΔS | Sheafified Cone; verifier replay H_* |
| 3 | Čech curvature (3‑window cover) | δg=c; δc=1; ℓ(c) finite | Refine cover descent; edit‑path logs |
| 4 | One motive lift (eligible only) | reg=per; comp_{B,dR} (example) | Gal descent and binding verified |
| 5 | Sealed pushout bundle | H_τ reproduced; terminality | Kan descent; full Merkle tree in JSON |

**Observables / Invariants (Dashboard‑Safe, Proof‑Backed)**
| Layer | Observable | Type | Source of Truth | Descent/Audit Extension |
|:--|:--|:--|:--|:--|
| Echo | b_k = dim H_k(Cone(U)) | ℕ^k | Homology in Ch(𝓟) | Restriction‑invariant; Merkle siblings |
| Echo | Graded ΔS | ℝ | Associated‑graded via Fᵏ(q‑CRO) | Pullback‑stable; priors logged |
| Curvature | ℓ(c_{ijk}) | ℕ | Edit metric in G | Constant on descent classes; path logs |
| Timefold | KL(μ_t‖μ_{−t}) | ℝ₊ | Regularized symbol measures | Prior + window recorded |
| Motive | per, reg, per_p | ℝ, ℚ_p | Built variety + comparison | Gal‑invariant; spec replayable |
| Sealing | H_τ | 256‑bit | Verifier pushout replay | Full Merkle tree JSON |

**Core Lean Obligations**
| File/Lemma | Statement | Scope | Descent/Audit Add‑On |
|:--|:--|:--|:--|
| ConeIdAcyclic.lean | H•(Cone(id_C)) = 0 | Echo base | Acyclicity descends; proof exported |
| CechIdentities.lean | δg=c and δc=1 | Curvature | Refinement‑stable; G‑action proved |
| MotiveExample.lean | reg(R)=per(R); comp_{B,dR} iso | Arithmetic module | Gal‑equivariant; binding lemma |
| PushoutDescent.lean | Kan extension preserves invariants | Sealing | Extension replay verified |
| EntanglementFlat.lean | Obs(CRO⊗Ent) monotone; curvature(𝒟)=0 | Diagnostics | Naturality + monotonicity proofs |

**Acceptance Criteria**
| Criterion | Check | Descent/Audit Add‑On |
|:--|:--|:--|
| Substrate frozen | Types compile | Fibration descent + iso groupoid |
| Cone works | Cone(id) acyclic | Descent for cones; H_* Merkle |
| Echo measured | Betti ≥ 0; ΔS present | Sheaf restriction logs; priors |
| Čech valid | δg=c; δc=1; ℓ(c) finite | Finer cover descent; edit paths |
| Motive honest | Example passes; eligible only | Gal actions; variety replay |
| Seal reproducible | H_τ matches on replay | Kan descent; full tree JSON |
