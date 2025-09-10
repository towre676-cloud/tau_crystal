# Residual Symmetry Grid (τ-Crystal receipts)

Windows: θ₁₂∈[20°,40°], θ₁₃∈[5°,12°], θ₂₃∈[35°,55°], |δ|≤10°.

| ok | template | params | θ12 | θ13 | θ23 | δ | witnesses | receipt |
|:--:|:--|:--|:--:|:--:|:--:|:--:|:--|:--|
| ❌ | — | — | — | — | — | — | — | `campaigns/residuals_20250910_181553Z/receipts/TM1_b10.0.receipt.json` |
| ❌ | — | — | — | — | — | — | — | `campaigns/residuals_20250910_181553Z/receipts/TM1_b12.5.receipt.json` |
| ❌ | — | — | — | — | — | — | — | `campaigns/residuals_20250910_181553Z/receipts/TM1_b7.5.receipt.json` |
| ❌ | — | — | — | — | — | — | — | `campaigns/residuals_20250910_181553Z/receipts/TM2_b10.0.receipt.json` |
| ❌ | — | — | — | — | — | — | — | `campaigns/residuals_20250910_181553Z/receipts/TM2_b12.5.receipt.json` |
| ❌ | — | — | — | — | — | — | — | `campaigns/residuals_20250910_181553Z/receipts/TM2_b7.5.receipt.json` |
| ❌ | — | — | 48.23 | 22.66 | 48.23 | 0.00 | — | `campaigns/residuals_20250910_181553Z/receipts/cp_residual.receipt.json` |
| ❌ | Z3_TBM,Z2_mu_tau_reflection | theta13_deg=9.0 | 35.60 | 7.34 | 5.22 | 0.00 | fail:mu_tau_moduli_equal | `campaigns/residuals_20250910_181553Z/receipts/cp_residual_symm.mu_tau.receipt.json` |
| ❌ | Z3_TBM,Z2_mu_tau_with_CP | theta13_deg=9.0 | 41.81 | 4.98 | 3.97 | 0.00 | all✓ | `campaigns/residuals_20250910_181553Z/receipts/cp_residual_symm.receipt.json` |
| ❌ | Z3_TBM,TM1 | theta13_deg=9.0, beta_deg=10.0 | 0.00 | 0.00 | 10.00 | 0.00 | fail:mu_tau_moduli_equal,tm1_preserved_col1,tm2_preserved_col2 | `campaigns/residuals_20250910_181553Z/receipts/cp_residual_symm.tm1.receipt.json` |
| ❌ | Z3_TBM,TM2 | theta13_deg=9.0, beta_deg=10.0 | 0.00 | 10.00 | 0.00 | 0.00 | fail:mu_tau_moduli_equal,tm1_preserved_col1,tm2_preserved_col2 | `campaigns/residuals_20250910_181553Z/receipts/cp_residual_symm.tm2.receipt.json` |
| ✅ | — | — | 28.87 | 6.35 | 45.35 | 0.00 | — | `campaigns/residuals_20250910_181553Z/receipts/cp_unitary.receipt.json` |
| ✅ | — | — | — | — | — | — | — | `campaigns/residuals_20250910_181553Z/receipts/delta27.receipt.json` |
| ✅ | — | — | — | — | — | — | — | `campaigns/residuals_20250910_181553Z/receipts/fermion_ratios.receipt.json` |
| ✅ | — | — | — | — | — | — | — | `campaigns/residuals_20250910_181553Z/receipts/tm1_sumrule.receipt.json` |
| ✅ | — | — | — | — | — | — | — | `campaigns/residuals_20250910_181553Z/receipts/tm2_sumrule.receipt.json` |
| ❌ | — | — | — | — | — | — | — | `analysis/TM1_b10.0.receipt.json` |
| ❌ | — | — | — | — | — | — | — | `analysis/TM1_b12.5.receipt.json` |
| ❌ | — | — | — | — | — | — | — | `analysis/TM1_b7.5.receipt.json` |
| ❌ | — | — | — | — | — | — | — | `analysis/TM2_b10.0.receipt.json` |
| ❌ | — | — | — | — | — | — | — | `analysis/TM2_b12.5.receipt.json` |
| ❌ | — | — | — | — | — | — | — | `analysis/TM2_b7.5.receipt.json` |
| ❌ | — | — | 48.23 | 22.66 | 48.23 | 0.00 | — | `analysis/cp_residual.receipt.json` |
| ❌ | Z3_TBM,Z2_mu_tau_reflection | theta13_deg=9.0 | 35.60 | 7.34 | 5.22 | 0.00 | fail:mu_tau_moduli_equal | `analysis/cp_residual_symm.mu_tau.receipt.json` |
| ❌ | Z3_TBM,Z2_mu_tau_with_CP | theta13_deg=9.0 | 41.81 | 4.98 | 3.97 | 0.00 | all✓ | `analysis/cp_residual_symm.receipt.json` |
| ❌ | Z3_TBM,TM1 | theta13_deg=9.0, beta_deg=10.0 | 0.00 | 0.00 | 10.00 | 0.00 | fail:mu_tau_moduli_equal,tm1_preserved_col1,tm2_preserved_col2 | `analysis/cp_residual_symm.tm1.receipt.json` |
| ❌ | Z3_TBM,TM2 | theta13_deg=9.0, beta_deg=10.0 | 0.00 | 10.00 | 0.00 | 0.00 | fail:mu_tau_moduli_equal,tm1_preserved_col1,tm2_preserved_col2 | `analysis/cp_residual_symm.tm2.receipt.json` |
| ✅ | — | — | 28.87 | 6.35 | 45.35 | 0.00 | — | `analysis/cp_unitary.receipt.json` |
| ✅ | — | — | — | — | — | — | — | `analysis/delta27.receipt.json` |
| ✅ | — | — | — | — | — | — | — | `analysis/fermion_ratios.receipt.json` |
| ✅ | — | — | — | — | — | — | — | `analysis/tm1_sumrule.receipt.json` |
| ✅ | — | — | — | — | — | — | — | `analysis/tm2_sumrule.receipt.json` |

## Integrity
- Each receipt includes `input_sha256` (contract) and `request_sha256` (dispatch request).
- Past receipts are immutable; new hypotheses use new contracts.
- Falsification is scientifically valuable: templates that fail under fixed windows are recorded as such.