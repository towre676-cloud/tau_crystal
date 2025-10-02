# Validation Protocol for Meaningfulness (Pre-Registered)

**Nulls:**  
N0: synthetic rationals with matched marginal heights/denominators;  
N1: subject–rational permutation.

**Tests & thresholds (fixed):**  
- M1: K≤2.0; isogeny ≥0.95 (10 recaptures/subject).  
- M2: KS(log N) vs N0/N1: reject at p<0.01 (D≥0.10); ST sup-norm closer by ≥3σ; collisions ≥2 (k=50, ℓ=3) ⇒ clustering; MDL gain ≥10%.  
- M3: EMD(log N) ≤0.05 across LLL caps (5e3,1e4,2e4) and index sets A/B; isogeny ≥0.95.  
- M4: cross-device/lighting: isogeny ≥0.95; QS shifts ≤0.1.  
- M5: prereg ridge for log N; uplift ≥5σ vs N0/N1; MDL reduction ≥10%.  
- M6: PCA-SVD vs Procrustes: isogeny ≥0.95.  
- M7: adversarial ∥δL∥₂ ≥0.5 mm median to flip isogeny.  
- M8: independent replication of M1–M7.

**Decision rule:** all pass ⇒ mapping meaningful. Any fail ⇒ artifact-dominated. Infrastructure claims unaffected.
