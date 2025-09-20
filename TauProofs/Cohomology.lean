import TauProofs.Leaf

namespace TauProofs

open scoped BigOperators

variable {α β γ : Type*}

/-- Cocycle law (statement only; proof to be added). -/
axiom cocycle
  (φ : α → β) (ψ : β → γ)
  (A : Finset α) (B : Finset β) (C : Finset γ) :
  delta (ψ ∘ φ) A C = (pushforward ψ) (delta φ A B) + delta ψ B C

end TauProofs
