import TauProofs.Leaf
import Mathlib.Data.Int.Basic
import Mathlib.Algebra.BigOperators.Basic

namespace TauProofs

open scoped BigOperators

variable {β : Type*}

/-- Keep τ as a plain functional for now; we can upgrade to AddMonoidHom later. -/
abbrev TauFunctional (β : Type*) := FreeAbelianGroup β → Int

/-- L1 seminorm placeholder on a chosen finite support (to be defined/proved). -/
axiom l1Norm (S : Finset β) : FreeAbelianGroup β → Nat

/-- Lipschitz inequality for τ (statement stub). -/
axiom lipschitz
  (τ : TauFunctional β) (Λ : Nat) (S : Finset β) (x : FreeAbelianGroup β) :
  Int.natAbs (τ x) ≤ Λ * l1Norm S x

/-- τ-conservativity when delta vanishes (statement stub). -/
axiom conservative
  (τ : TauFunctional β) (x : FreeAbelianGroup β) :
  x = 0 → τ x = 0

end TauProofs
