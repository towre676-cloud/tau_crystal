import TauProofs.Leaf
import Mathlib.Data.Int.Basic

namespace TauProofs

variable {β : Type*}

/-- Keep τ as a plain functional for now; can upgrade later. -/
abbrev TauFunctional (β : Type*) := FreeAbelianGroup β → Int

/-- L1 seminorm placeholder on a chosen list support. -/
axiom l1NormList (S : List β) : FreeAbelianGroup β → Nat

/-- Lipschitz inequality for τ (list version; statement stub). -/
axiom lipschitzList
  (τ : TauFunctional β) (Λ : Nat) (S : List β) (x : FreeAbelianGroup β) :
  Int.natAbs (τ x) ≤ Λ * l1NormList S x

/-- τ-conservativity when x=0. -/
axiom conservative
  (τ : TauFunctional β) (x : FreeAbelianGroup β) :
  x = 0 → τ x = 0

end TauProofs
