import TauProofs.Leaf

namespace TauProofs

variable {α β γ : Type*}

/-- Cocycle law (list form; proof added next). -/
axiom cocycleList
  (φ : α → β) (ψ : β → γ)
  (A : List α) (B : List β) (C : List γ) :
  deltaList (ψ ∘ φ) A C = (pushforward ψ) (deltaList φ A B) + deltaList ψ B C

end TauProofs
