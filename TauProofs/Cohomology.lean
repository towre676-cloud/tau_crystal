import TauProofs.Leaf

namespace TauProofs

variable {α β γ : Type*}

/-- Cocycle law (list form): Δ_{ψ∘φ} = ψ₊(Δ_φ) + Δ_ψ. -/
theorem cocycleList
  (φ : α → β) (ψ : β → γ)
  (A : List α) (B : List β) (C : List γ) :
  deltaList (ψ ∘ φ) A C = (pushforward ψ) (deltaList φ A B) + deltaList ψ B C := by
  -- Expand RHS, then cancel (a - b) + (b - c) = a - c, then use pushforward composition
  have h_sum :
      (pushforward ψ) (deltaList φ A B) + deltaList ψ B C
      =
      (pushforward ψ) ((pushforward φ) (unitOnList A)) - unitOnList C := by
    -- expand both deltas and push map through sub as add+neg
    -- (a - b) + (b - c) = a - c
    simpa [deltaList, sub_eq_add_neg] using
      (sub_add_sub_cancel
        ((pushforward ψ) ((pushforward φ) (unitOnList A)))
        ((pushforward ψ) (unitOnList B))
        (unitOnList C))
  have h_comp :
      (pushforward (ψ ∘ φ)) (unitOnList A)
      =
      (pushforward ψ) ((pushforward φ) (unitOnList A)) := by
    -- from pushforward_comp, specialize at unitOnList A
    have := congrArg (fun f => f (unitOnList A)) (pushforward_comp (φ := φ) (ψ := ψ))
    -- ((ψ)∘(φ)) on unit equals ψ₊(φ₊(unit))
    -- but `pushforward_comp` gives (ψ₊ ∘ φ₊) = (ψ∘φ)₊, so rewrite:
    simpa using this.symm
  -- Now rewrite RHS to Δ_{ψ∘φ}
  calc
    deltaList (ψ ∘ φ) A C
        = (pushforward (ψ ∘ φ)) (unitOnList A) - unitOnList C := rfl
    _   = (pushforward ψ) ((pushforward φ) (unitOnList A)) - unitOnList C := by simpa [h_comp]
    _   = (pushforward ψ) (deltaList φ A B) + deltaList ψ B C := by
          simpa [h_sum]  -- invert the equality from h_sum

end TauProofs
