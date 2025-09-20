/-! τ functional skeleton: hom + Lipschitz/conservativity statements. -/
import TauProofs.Leaf
import Mathlib.Algebra.Group.Hom
import Mathlib.Data.Int.Basic
import Mathlib.Tactic

namespace TauProofs

open scoped BigOperators

variable {β : Type _}

/-- A τ functional is an additive hom to ℤ. -/
abbrev TauFunctional (β : Type _) := FreeAbelianGroup β →+ ℤ

/-- Placeholder L1 seminorm on FreeAbelianGroup β relative to a chosen finite support.
    (Exact definition can be added later; for now we keep a symbolic signature.) -/
axiom l1Norm (S : Finset β) : FreeAbelianGroup β → ℕ

/-- Lipschitz inequality for τ (statement only, to be proven later). -/
axiom lipschitz
  (τ : TauFunctional β) (Λ : ℕ) (S : Finset β) (x : FreeAbelianGroup β) :
  Int.natAbs (τ x) ≤ Λ * l1Norm S x

/-- τ-conservativity when delta vanishes (statement only). -/
axiom conservative
  (τ : TauFunctional β) (x : FreeAbelianGroup β) :
  x = 0 → τ x = 0

end TauProofs
