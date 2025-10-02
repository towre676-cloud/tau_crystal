import Mathlib.Algebra.FreeAbelianGroup
import Mathlib.Data.Int.Basic
import Mathlib.Data.List.Basic

namespace TauProofs
open FreeAbelianGroup

/-- τ as an additive hom to ℤ. -/
abbrev TauFunctional (β : Type*) := FreeAbelianGroup β →+ Int

/-- Sum of basis generators over a list (simple recursion). -/
def unitFromList {β : Type*} : List β → FreeAbelianGroup β
  | []      => 0
  | b :: S  => of b + unitFromList S

/-- Back‑compat alias if other files referenced `unitOnList`. -/
abbrev unitOnList {β : Type*} := @unitFromList β

/-- Lipschitz bound for τ on a list of unit basis hits: if each basis
    contribution is bounded by `Λ`, then `|τ(∑ e_b)| ≤ Λ · |S|`. -/
theorem lipschitz_unitFromList
  {β : Type*} (τ : TauFunctional β) (Λ : Nat) :
  ∀ (S : List β),
    (∀ b ∈ S, Int.natAbs (τ (of b)) ≤ Λ) →
    Int.natAbs (τ (unitFromList S)) ≤ Λ * S.length
  | [], _ => by
      simp [unitFromList]
  | b :: S, h => by
      have hb  : Int.natAbs (τ (of b)) ≤ Λ := h b (by simp)
      have hS  : ∀ b
        intro b
        intro hb; exact h b
          (by simp [hb])
      have ih : Int.natAbs (τ (unitFromList S)) ≤ Λ * S.length :=
        lipschitz_unitFromList (β:=β) τ Λ S hS
      have addτ :
        τ (unitFromList (b :: S))
          = τ (of b) + τ (unitFromList S) := by
        simp [unitFromList, map_add]
      calc
        Int.natAbs (τ (unitFromList (b :: S)))
            = Int.natAbs (τ (of b) + τ (unitFromList S)) := by
                simpa [addτ]
        _ ≤ Int.natAbs (τ (of b)) + Int.natAbs (τ (unitFromList S)) := by
                simpa using Int.natAbs_add_le (τ (of b)) (τ (unitFromList S))
        _ ≤ Λ + Λ * S.length := by exact add_le_add hb ih
        _ = Λ * S.length + Λ := by simp [Nat.add_comm]
        _ = Λ * (Nat.succ S.length) := by
              simpa [Nat.succ_eq_add_one, Nat.mul_succ]
        _ = Λ * (List.length (b :: S)) := by simp

/-- Alias statement for callers that used `unitOnList`. -/
theorem lipschitz_unitOnList
  {β : Type*} (τ : TauFunctional β) (Λ : Nat) :
  ∀ (S : List β),
    (∀ b ∈ S, Int.natAbs (τ (of b)) ≤ Λ) →
    Int.natAbs (τ (unitOnList S)) ≤ Λ * S.length := by
  intro S h; simpa [unitOnList] using
    lipschitz_unitFromList (β:=β) τ Λ S h

end TauProofs
