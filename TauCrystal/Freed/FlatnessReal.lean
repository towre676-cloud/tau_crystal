/-
  TauCrystal.Freed.FlatnessReal

  Real-valued RG composition and a blueprint for the flatness identity
  d/dt log det Σ = tr(Σ⁻¹ · Σ').
-/

import Mathlib.Data.Real.Basic

namespace TauCrystal.Freed

/-- One-loop RG leaf over ℝ. -/
def muOneLoop (b μ0 ℓ : ℝ) : ℝ :=
  μ0 / (1 - b * μ0 * ℓ)

/--
RG functoriality (one-loop, rational identity):

  μ(ℓ₁ + ℓ₂; b, μ0) = μ(ℓ₂; b, μ(ℓ₁; b, μ0))

Assume denominators are nonzero at the evaluation point.
-/
theorem compose_real
  (b μ0 ℓ₁ ℓ₂ : ℝ)
  (h1  : 1 - b * μ0 * ℓ₁      ≠ 0)
  (h12 : 1 - b * μ0 * (ℓ₁+ℓ₂) ≠ 0)
  : muOneLoop b μ0 (ℓ₁ + ℓ₂)
    = muOneLoop b (muOneLoop b μ0 ℓ₁) ℓ₂ := by
  /- Sketch:
     RHS = (μ0 / (1 - b μ0 ℓ₁)) / (1 - b (μ0/(1 - b μ0 ℓ₁)) ℓ₂)
         = μ0 / (1 - b μ0 (ℓ₁ + ℓ₂)).
     A standard `field_simp`/`ring_nf` proof discharging `h1`, `h12`.
  -/
  sorry

/--
Blueprint (to formalize with Mathlib):

If Σ : ℝ → GL(n, ℝ) is C¹ and SPD for all t, then

  d/dt (Real.log (Matrix.det (Σ t))) = Matrix.trace (Matrix.inv (Σ t) ⬝ deriv Σ t)

This is the Bismut–Freed flatness identity reflected in receipts.
-/
-- theorem flatness_trace_logdet ... := by
--   /- derivative of det + chain rule for log, plus SPD ⇒ invertible -/
--   sorry

end TauCrystal.Freed
