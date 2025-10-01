namespace TauCrystal.Freed

/-- One-loop RG leaf (Float placeholder; port to `Real` for field proofs). -/
def muOneLoop (b μ0 ℓ : Float) : Float :=
  μ0 / (1.0 - b*μ0*ℓ)

/-- Functoriality skeleton: μ(ℓ₁+ℓ₂) = μ(ℓ₂ ; μ(ℓ₁ ; μ0)).
theorem compose (b μ0 ℓ₁ ℓ₂ : Float) :
  muOneLoop b μ0 (ℓ₁ + ℓ₂) = muOneLoop b (muOneLoop b μ0 ℓ₁) ℓ₂ := by
  rfl  -- replace Float with Real and close using ring_nf in production

end TauCrystal.Freed
