# Meaningfulness Criteria (M1–M8) for Face→Curve Mapping

**Scope.** T1–T4 (integrality, multiplicativity, Ramanujan, stability) certify arithmetic hygiene only.
The mapping is **meaningful** iff it passes **all** M1–M8 against explicit nulls (N0, N1):

M1 Invariance & Continuity: Lipschitz bound (K≤2.0) and ≥0.95 isogeny stability under admissible noise.  
M2 Null Separation: Faces differ from N0/N1 on ≥2 of (KS on log N, Sato–Tate sup norm, isogeny collisions, MDL gain ≥10%).  
M3 Knob Robustness: EMD(log N) ≤ 0.05 across LLL caps/index sets; isogeny stability ≥0.95.  
M4 Hardware Generalization: cross-device/lighting isogeny stability ≥0.95; QS shifts ≤0.1.  
M5 Predictivity/MDL: conditional codelength reduction ≥10% and ≥5σ uplift vs N0/N1 for out-of-sample log N.  
M6 Alternative Canonicalizers: PCA-SVD vs Procrustes agree up to isogeny ≥0.95.  
M7 Adversarial Margin: minimal perturbation to flip isogeny ≥0.5 mm median.  
M8 Cross-Lab Replication: independent lab reproduces M1–M7.

**Decision:** any failure ⇒ mapping labeled *artifact-dominated*. Instrument claims remain; biometric meaning withdrawn.
