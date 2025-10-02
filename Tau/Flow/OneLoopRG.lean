import Mathlib

namespace Tau.Flow

/-- One-loop RG with inverse-coupling linearization: 1/μ + bℓ = 1/μ₀. -/
structure OneLoopRG where
  mu  : ℝ
  mu0 : ℝ
  b   : ℝ
  ell : ℝ

namespace OneLoopRG

/-- Constraint invariant. -/
def invariant (r : OneLoopRG) : ℝ := (1 / r.mu) + r.b * r.ell - (1 / r.mu0)

/-- Entropy-like delta S(ℓ) = μ(ℓ) - μ₀. -/
def S (r : OneLoopRG) : ℝ := r.mu - r.mu0

/-- Landau pole ℓ* = 1/(b μ₀), when defined. -/
def pole (r : OneLoopRG) : Option ℝ :=
  if r.b ≠ 0 ∧ r.mu0 ≠ 0 then some (1 / (r.b * r.mu0)) else none

theorem S_nonneg_of_mu_ge_mu0 {r : OneLoopRG} (h : r.mu ≥ r.mu0) : r.S ≥ 0 := by
  dsimp [S]; exact sub_nonneg_of_le h

end OneLoopRG
end Tau.Flow
