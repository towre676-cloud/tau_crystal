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
