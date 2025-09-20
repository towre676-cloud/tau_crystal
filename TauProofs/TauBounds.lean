import TauProofs.Leaf
import Mathlib.Data.Int.Basic
import Mathlib.Data.List.Basic

namespace TauProofs

variable {β : Type*}

/-- τ as an additive hom to ℤ. -/
abbrev TauFunctional (β : Type*) := FreeAbelianGroup β →+ Int

/-- Basic Lipschitz lemma for inputs of the form `unitOnList S`.
If each basis contribution is bounded by Λ, then
  |τ(∑_{a∈S} e a)| ≤ Λ * |S|. -/
theorem lipschitz_unitOnList
  (τ : TauFunctional β) (Λ : Nat) :
  ∀ (S : List β), (∀ b ∈ S, Int.natAbs (τ (e b)) ≤ Λ) →
    Int.natAbs (τ (unitOnList S)) ≤ Λ * S.length
  | [], _ => by
      simp [unitOnList]
  | a :: t, h => by
      have hb : Int.natAbs (τ (e a)) ≤ Λ :=
        h a (List.mem_cons_self _ _)
      have ht : ∀ b ∈ t, Int.natAbs (τ (e b)) ≤ Λ :=
        fun b hb' => h b (List.mem_cons_of_mem _ hb')
      have ih := lipschitz_unitOnList t ht
      -- τ(unitOnList (a::t)) = τ(unitOnList t + e a) = τ(unitOnList t) + τ(e a)
      calc
        Int.natAbs (τ (unitOnList (a :: t)))
            = Int.natAbs (τ (unitOnList t + e a)) := by simp [unitOnList]
        _   = Int.natAbs (τ (unitOnList t) + τ (e a)) := by
                simpa [map_add]  -- additivity of τ
        _   ≤ Int.natAbs (τ (unitOnList t)) + Int.natAbs (τ (e a)) :=
                Int.natAbs_add_le _ _
        _   ≤ Λ * t.length + Λ := by exact add_le_add ih hb
        _   = Λ * (t.length + 1) := by
                -- Λ * t.length + Λ = Λ * (t.length + 1)
                simpa [Nat.mul_add, Nat.mul_one, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
        _   = Λ * (List.length (a :: t)) := by simp

end TauProofs
