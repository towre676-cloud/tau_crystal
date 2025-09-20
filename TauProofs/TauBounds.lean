import TauProofs.Leaf
import Mathlib.Algebra.Group.Hom
import Mathlib.Data.Int.Basic

namespace TauProofs

open scoped BigOperators

variable {β : Type _}

/-- A τ functional is an additive hom to ℤ. -/
abbrev TauFunctional (β : Type _) := FreeAbelianGroup β →+ ℤ

/-- L1 seminorm placeholder on a chosen finite support (to be defined/proved). -/
axiom l1Norm (S : Finset β) : FreeAbelianGroup β → ℕ

/-- Lipschitz inequality for τ (statement stub). -/
axiom lipschitz
  (τ : TauFunctional β) (Λ : ℕ) (S : Finset β) (x : FreeAbelianGroup β) :
  Int.natAbs (τ x) ≤ Λ * l1Norm S x

/-- τ-conservativity when the delta vanishes (statement stub). -/
axiom conservative
  (τ : TauFunctional β) (x : FreeAbelianGroup β) :
  x = 0 → τ x = 0

end TauProofs
