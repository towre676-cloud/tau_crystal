import Mathlib

namespace Tau.Flow

/-- Hex scheduler N(ℓ) = (1/(6b)) * log(1/|1 - b μ₀ ℓ|). -/
def N (b mu0 ell : ℝ) : ℝ :=
  (1 / (6 * b)) * Real.log (1 / |1 - b * mu0 * ell|)

/-- Wall times ℓ_k = (1/(b μ₀)) (1 - exp(-3 b k)). -/
def ell_k (b mu0 k : ℝ) : ℝ := (1 / (b * mu0)) * (1 - Real.exp (-3 * b * k))

end Tau.Flow
