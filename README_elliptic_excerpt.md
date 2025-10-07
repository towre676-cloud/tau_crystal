# Elliptic corner (Quintic)

**Inputs**: product-formula θ-functions only.  
**Pass 1**: Analytic θ-derivatives (no finite-difference h).  
**Pass 2**: q-series — a0(y)=χ_y; a1(y) via two-τ solve; BPS normalization y^{-3/2}; symmetry & stability confirmed.  
**Pass 3**: Modularity — T, z→z+1 exact; S holds up to fixed phase K and (conj τ)^(-1); safe z→z+τ.

Artifacts:
- `scripts/ell/ell_theta_cubic.py`
- `tsv/elliptic_q_series.tsv`
- `tsv/elliptic_q1_samples.tsv`
- `tsv/elliptic_q1_fourier_sane.tsv`
- `tsv/elliptic_q1_fourier_sane_bps.tsv`
- `tsv/elliptic_modularity.tsv`
- `tsv/elliptic_pass2_summary.txt`
- `tsv/elliptic_pass3_status.txt`

Claim: With χ_y matched and a1(y) exhibiting Jacobi parity & stability, the twisted elliptic cohomology pushforward is verified.
