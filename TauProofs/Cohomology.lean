/-! Cohomology skeleton: cocycle law statement. -/
import TauProofs.Leaf
import Mathlib.Algebra.Group.Defs

namespace TauProofs

open scoped BigOperators

variable {α β γ : Type _}

/-- Cocycle law (statement only for now). -/
axiom cocycle
  (φ : α → β) (ψ : β → γ)
  (A : Finset α) (B : Finset β) (C : Finset γ) :
  delta (ψ ∘ φ) A C = (pushforward ψ) (delta φ A B) + delta ψ B C

end TauProofs
