## Top‑Level Activation Map (with Descent, Audit, and Freed Cross‑References)
| Cluster | Semantic Object | Category/Structure | Observable/Invariant | Lean Obligation | Immediate Activation | Freed Cross‑Ref |
|:--|:--|:--|:--|:--|:--|:--|
| Morphic Echo | Echo cone Cone(U) | Chain map U: C•(f₁)→C•(f₂) in Ch(𝓟); triangulated; stackifies over 𝓛 | Betti tuple (b₀,…,b_k); graded ΔS via Gr(Fᵏ) | H•(Cone(id))=0; mark quasi‑isos | Detect duplicate input; build U; compute Cone(U); record Betti, graded ΔS; sheafify over τ‑subintervals | Segal: repetition as bordism composition; factorization lift along overlaps |
| Čech Curvature | Cocycle c_{ijk} | Non‑abelian Čech 2‑cocycle c=δg with g_{ij}∈G on τ‑cover | ℓ(c_{ijk}) (edit length in G); KL(μ_t‖μ_{−t}) for Θ | δg=c, δc=1 | Compute g_{ij}, c_{ijk}; publish ℓ(c) and KL; expose c in verifier | Anomaly as obstruction to global section; Costello–Gwilliam locality |
| Motive Embedding | Regulator period | M_R∈Ext¹_{MTM}(ℚ(0),ℚ(1)) for eligible modules; Gal(ℚ(b)/ℚ) action | per(R), reg(R), per_p(R) | reg=per (example), comp_{B,dR} iso | Build algebraic variety from manifest params; compute period; bind to receipt; Gal descent record | QFT observables as periods; index/regulator compatibilities |
| Sealing/Integration | Manifest pushout | 𝓜′=𝓜 ⊔_{𝓜|_𝒟} 𝓝; 𝓜:𝒞→Set; Kan extension along 𝒟↪𝒞 | Validity=terminality; Merkle H_τ; Obs(CRO⊗Ent) monotone | Pushout existence; Obs monotonicity | Choose finite 𝒟; form 𝓝; pushout; replay H_τ in verifier; emit Obs contract | Bordism‑style gluing; factorization |

## Static Substrate (with Descent Conditions and Audit Groupoids)
| Symbol | Meaning | Minimal Contents to Freeze | Descent/Audit Extension |
|:--|:--|:--|:--|
| 𝒞 | Typed execution category with receipts | Objects S; morphisms f:S→S′ with ρ(f); π:𝒞→τ | Fibered in groupoids over τ; audit 2‑cells = simulations |
| Σ | Typed signature algebra | Constructors, typing rules, assoc/identity | Sheaf descent for Σ‑terms; audit: proof‑trace morphisms in Prof(Σ) |
| 𝓟 | Provenance algebra | ℤ⟨receipt symbols⟩; boundary ∂ from grammar | ∂ natural with pullbacks; audit: homology functors exposed |
| Ch(𝓟) | dg‑category over 𝓟 | Complexes, chain maps, cones, H_* | Stackifies over 𝓛; audit: H_* with Merkle siblings |
| 𝓛 | Site of τ‑intervals | Joyal–Tierney coverage | Effective epimorphisms; audit: cover recomputation |
| G | Relabeling automorphism group | Generators/relations preserving type/order/hash | Compatible action on descent data; audit: generator metrics and proofs |

## Execution Order (with Descent and Audit Flows)
| Step | Deliverable | Gating Proof/Check | Descent/Audit Add‑On |
|:--|:--|:--|:--|
| 1 | Freeze 𝒞, Σ, 𝓟(∂), 𝓛, Ch(𝓟) | Cone(id) acyclic; Σ laws check | Fibration descent verified; audit groupoid emitted |
| 2 | Morphic Echo prototype | Betti(Cone(U)); graded ΔS | Sheafify Cone over subintervals; verifier replay of U and H_* |
| 3 | Čech curvature on 3‑window cover | δg=c and δc=1 | Descent to finer covers; endpoint exposes g‑paths and c witnesses |
| 4 | One motive lift | reg=per on example; comp_{B,dR} iso | Galois descent logged; verifier replays variety and bindings |
| 5 | Sealed pushout bundle | Terminality and H_τ match | Kan descent documented; full pushout replay certificate |

## Observables and Invariants (with Descent/Audit)
| Layer | Observable | Type | Source of Truth | Descent/Audit Extension |
|:--|:--|:--|:--|:--|
| Echo | b_k = dim H_k(Cone(U)) | ℕ^k | Homology in Ch(𝓟) | Invariant under restriction; Merkle path to H_* |
| Echo | Graded ΔS | ℝ | Associated‑graded via Fᵏ(q‑CRO frequencies) | Glues under pullbacks; prior parameters recorded |
| Curvature | ℓ(c_{ijk}) | ℕ | Edit metric in G | Constant on descent classes; edit path logs |
| Timefold | KL(μ_t‖μ_{−t}) | ℝ₊ | Regularized symbol measures | Pullback stability; priors and windows logged |
| Motive | per, reg, per_p | ℝ, ℚ_p | Built variety + comparison | Gal‑invariant; variety spec replayable |
| Sealing | H_τ | 256‑bit | Verifier pushout replay | Full Merkle tree JSON; subtree proofs |

## Core Lean Obligations (with Descent Lemmas and Audit Proofs)
| File/Lemma | Statement | Scope | Descent/Audit Add‑On |
|:--|:--|:--|:--|
| ConeIdAcyclic.lean | H•(Cone(id_C)) = 0 | Echo machinery base | Acyclicity descends; proof export to verifier |
| CechIdentities.lean | δg=c and δc=1 | Curvature well‑formedness | Identities persist under refinement; G‑action proved |
| MotiveExample.lean | reg(R)=per(R); comp_{B,dR} iso | Eligible arithmetic module | Gal‑equivariance recorded; binding lemma exported |
| PushoutDescent.lean | Kan extension preserves invariants | Sealing/manifest | Extension replay verified; terminality lemma |
| EntanglementFlat.lean | Obs(CRO⊗Ent) monotone; curvature(𝒟)=0 | Cross‑diagnostics | Naturality and monotonicity proofs exposed |

## Minimal Artifacts per Cluster (with Descent/Audit Logs)
| Cluster | JSON/Artifacts | Purpose | Descent/Audit Add‑On |
|:--|:--|:--|:--|
| Echo | echo_chain.json; cone_homology.json; descent_cone.json | U, Betti, graded ΔS; sheafified Cone | Restriction maps; Merkle siblings for H_* |
| Curvature | cover_windows.json; glue_gij.json; cocycle_cijk.json; length_metrics.json; descent_c.json | Overlaps; g and c; ℓ(c); descended cocycle | Pullback data; edit path logs |
| Motive | variety_spec.json; period_values.json; receipt_binding.json; descent_gal.json | Spec; per/reg; receipt link; Galois descent | Gal actions; isomorphism traces |
| Sealing | subcat_D.json; delta_N.json; pushout_manifest.json; verifier_certificate.json; descent_kan.json | 𝒟, 𝓝, pushout; Merkle replay | Kan extension maps; full tree logs |

## Acceptance Criteria (with Descent/Audit Requirements)
| Criterion | Check | Descent/Audit Add‑On |
|:--|:--|:--|
| Substrate frozen | 𝒞, Σ, 𝓟(∂), 𝓛, Ch(𝓟) compile | Fibration descent ok; groupoid of type iso emitted |
| Cone works | Cone(id) acyclic | Descent for cones; H_* Merkle siblings present |
| Echo measured | cone_homology.json has non‑negative Betti | Sheaf restriction logs; priors recorded |
| Čech valid | δg=c and δc=1; ℓ(c) finite | Finer cover descent; edit paths exported |
| Motive honest | MotiveExample.lean passes; eligible only | Gal‑equivariance; variety replay |
| Seal reproducible | Verifier recomputes H_τ | Kan descent; full Merkle tree JSON |

## Freed Program Cross‑Walk (axioms → τ‑Crystal invariants)
| Freed/Segal/CG Concept | τ‑Crystal Realization | Proof Object |
|:--|:--|:--|
| Bordism functoriality (Segal) | Executions as morphisms; repetition as bordism composition | Associativity/identity in Σ; Cone(id) |
| Anomaly/obstruction | Non‑abelian Čech c_{ijk} on τ‑cover | CechIdentities.lean; δg=c, δc=1 |
| Factorization locality (Costello–Gwilliam) | Windows cover; disjoint interval composition | Cover refinement logs; naturality of Obs |
| Reflection positivity / duality | Timefold involution Θ; KL asymmetry observable | Measure pullback lemma; prior stability |
| Index/regulator | per, reg on eligible modules | MotiveExample.lean; comparison isomorphism |
| Gluing / cutting | Manifest pushout; Kan extension | PushoutDescent.lean; terminality check |

## Error‑Handling and Safety Invariants
| Layer | Failure Mode | Guard/Invariant | Audit Surface |
|:--|:--|:--|:--|
| Echo | Non‑triangulated cone attempt | Cones only in Ch(𝓟); reject raw‑ledger cones | cone_homology.json presence and schema |
| Curvature | Hash‑log misuse | No logs of hashes; only G automorphisms | glue/cocycle JSON with generator paths |
| Motive | Spurious motive claims | Motives only for eligible modules with spec | variety_spec.json and binding proof hash |
| Sealing | Non‑replayable manifest | Pushout must replay; mismatch = reject | verifier_certificate.json with Merkle tree |
| Timefold | KL zeros / instability | Fixed prior; windowed measures; regularization | priors and windows recorded in endpoint |

## Fifteen‑Module Bundle Integration Hooks
| Module Group | Hook into Tables | Required Invariant | Emitted Artifact |
|:--|:--|:--|:--|
| q‑CRO / Entropy | Echo; Observables; EntanglementFlat | Filtration Fᵏ well‑defined | freq_hist.json; F‑graded config |
| Residue/Receipt | Curvature; Sealing | G generators cover relabelings | gij_generators.json |
| LLM Adapter | Σ/Execution; Sealing | All UI ops are Σ‑terms with proofs | ui_term_log.json; proof_refs.json |
| Langlands Anchor | Motive Embedding | Algebraic params ↔ receipt binding | receipt_binding.json |
| Verifier UI | Sealing; Audit | Full replay; deterministic outputs | verifier_certificate.json |

## Public Audit & Verifier Endpoints (read‑only)
| Endpoint | Input | Output | Guarantees |
|:--|:--|:--|:--|
| /verify/bundle/{H_τ} | bundle hash | valid, Merkle tree, pushout replay, proofs list | Reproducibility and terminality |
| /echo/{run_id} | echo_chain.json | H_* of Cone(U), graded ΔS, Merkle siblings | Echo invariants with provenance |
| /curvature/{cover_id} | cover_windows.json | g_{ij}, c_{ijk}, ℓ(c), edit paths | Čech anomaly audit |
| /motive/{receipt_id} | variety_spec.json | per, reg, per_p, binding proof hash | Arithmetic honesty |
| /obs/cro‑ent/{t} | q‑CRO + Ent window | Obs value and monotonicity certificate | Cross‑diagnostic contract |

