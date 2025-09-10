# Residual Symmetry Falsification (τ-Crystal receipts)

**Windows (pre-committed):** θ₁₂∈[20°,40°], θ₁₃∈[5°,12°], θ₂₃∈[35°,55°], |δ|≤10°.

## Results
| ok | template | params | θ12 | θ13 | θ23 | δ | witnesses | receipt |
|:--:|:--|:--|:--:|:--:|:--:|:--:|:--|:--|
| ❌ | — | — | — | — | — | — | — | `analysis/TM1_b10.0.receipt.json` |
| ❌ | — | — | — | — | — | — | — | `analysis/TM1_b12.5.receipt.json` |
| ❌ | — | — | — | — | — | — | — | `analysis/TM1_b7.5.receipt.json` |
| ❌ | — | — | — | — | — | — | — | `analysis/TM2_b10.0.receipt.json` |
| ❌ | — | — | — | — | — | — | — | `analysis/TM2_b12.5.receipt.json` |
| ❌ | — | — | — | — | — | — | — | `analysis/TM2_b7.5.receipt.json` |
| ❌ | — | — | — | — | — | — | — | `analysis/auto_delta27.receipt.json` |
| ❌ | — | — | 48.23 | 22.66 | 48.23 | 0.00 | — | `analysis/cp_residual.receipt.json` |
| ❌ | Z3_TBM,Z2_mu_tau_reflection | theta13_deg=9.0 | 35.60 | 7.34 | 5.22 | 0.00 | fail:mu_tau_moduli_equal | `analysis/cp_residual_symm.mu_tau.receipt.json` |
| ❌ | Z3_TBM,Z2_mu_tau_with_CP | theta13_deg=9.0 | 41.81 | 4.98 | 3.97 | 0.00 | all✓ | `analysis/cp_residual_symm.receipt.json` |
| ❌ | Z3_TBM,TM1 | theta13_deg=9.0, beta_deg=10.0 | 0.00 | 0.00 | 10.00 | 0.00 | fail:mu_tau_moduli_equal,tm1_preserved_col1,tm2_preserved_col2 | `analysis/cp_residual_symm.tm1.receipt.json` |
| ❌ | Z3_TBM,TM2 | theta13_deg=9.0, beta_deg=10.0 | 0.00 | 10.00 | 0.00 | 0.00 | fail:mu_tau_moduli_equal,tm1_preserved_col1,tm2_preserved_col2 | `analysis/cp_residual_symm.tm2.receipt.json` |
| ✅ | — | — | 28.87 | 6.35 | 45.35 | 0.00 | — | `analysis/cp_unitary.receipt.json` |
| ✅ | — | — | — | — | — | — | — | `analysis/delta27.receipt.json` |
| ✅ | — | — | — | — | — | — | — | `analysis/fermion_ratios.receipt.json` |

## Integrity
- Each receipt includes `input_sha256` (contract) and `request_sha256` (dispatch request).
- Past receipts are immutable; new hypotheses use new contracts.
- Falsification is scientifically valuable: these templates systematically fail under fixed windows.
