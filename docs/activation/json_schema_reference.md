# JSON Schema Reference (Verifier‑Compatible Artifact Keys)

| Artifact | Key Fields | Invariant Type | Validation |
|:--|:--|:--|:--|
| echo_chain.json | run_id; f1_id; f2_id; diff_symbol_list | Ch(𝓟) chain structure | Complex well‑typed; ∂ consistency; Lean hash |
| cone_homology.json | betti:[…]; graded_ΔS | Homology from Cone(U) | H•(Cone(id))=0 proof present; Merkle siblings |
| cover_windows.json | windows:[(t0,t1),…] | τ‑cover spec | Overlaps total; refinement logs |
| glue_gij.json | pairs:[(i,j)]; gij: generators | Automorphisms in G | Generator paths valid; preserves type/order/hash |
| cocycle_cijk.json | triples:[(i,j,k)]; c_val; edit_length | Čech 2‑cocycle values | δg=c and δc=1 verified; edit path sound |
| length_metrics.json | metric:edit; lengths:[…] | Group metric report | Minimality witness; generator counts |
| variety_spec.json | field:ℚ(b); eqns:[…]; basepoints | Algebraic variety spec | Well‑formed; param link to manifest |
| period_values.json | per; reg; per_p; variety_name | Motivic regulator values | reg=per proof hash; Gal descent log |
| receipt_binding.json | receipt_id; param_map | Binding map | Surjective to used params; Lean lemma hash |
