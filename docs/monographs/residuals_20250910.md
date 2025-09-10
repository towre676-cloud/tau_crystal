# Residual Symmetry Falsification Campaign

Timestamp (UTC): 2025-09-10 18:03Z

Windows (pre-committed): θ₁₂∈[20°,40°], θ₁₃∈[5°,12°], θ₂₃∈[35°,55°], |δ|≤10°.

This page is generated from the frozen receipts. See the campaign folder for `artifacts.tgz` and `MANIFEST.sha256`.

## Results
- FAIL | — | — | θ12=48.23037077863336 θ13=22.661877435468313 θ23=48.23037077862779 δ=0.0 | `analysis/cp_residual.receipt.json`
- FAIL | Z3_TBM,Z2_mu_tau_reflection | theta13_deg=9.0 | θ12=35.599669422348285 θ13=7.338333669348276 θ23=5.224784442192721 δ=0.0 | `analysis/cp_residual_symm.mu_tau.receipt.json`
- FAIL | Z3_TBM,Z2_mu_tau_with_CP | theta13_deg=9.0 | θ12=41.807309520367866 θ13=4.977435543910886 θ23=3.9652300679756904 δ=0.0 | `analysis/cp_residual_symm.receipt.json`
- FAIL | Z3_TBM,TM1 | theta13_deg=9.0, beta_deg=10.0 | θ12=1.5902773407317586e-15 θ13=3.1805546814635168e-15 θ23=9.999999999999996 δ=0.0 | `analysis/cp_residual_symm.tm1.receipt.json`
- FAIL | Z3_TBM,TM2 | theta13_deg=9.0, beta_deg=10.0 | θ12=0.0 θ13=10.000000000000002 θ23=6.459239728231687e-15 δ=0.0 | `analysis/cp_residual_symm.tm2.receipt.json`
- PASS | — | — | θ12=28.874193606867504 θ13=6.350819042725543 θ23=45.354883151198564 δ=0.0 | `analysis/cp_unitary.receipt.json`