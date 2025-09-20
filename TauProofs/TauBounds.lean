import TauProofs.Leaf
import Mathlib.Data.Int.Basic
import Mathlib.Data.List.Basic

namespace TauProofs

variable {β : Type*}

/-- τ as an additive hom to ℤ. -/
abbrev TauFunctional (β : Type*) := FreeAbelianGroup β →+ Int

/-- Basic Lipschitz lemma for inputs of the form `unitOnList S`.
If each basis contribution is bounded by Λ, then
  |τ(∑ (a in S) e a)| ≤ Λ * |S|.  (List version, no big-ops.) -/
theorem lipschitz_unitOnList
  (τ : TauFunctional β) (Λ : Nat) :
  ∀ (S : List β), (∀ b ∈ S, Int.natAbs (τ (e b)) ≤ Λ) →
    Int.natAbs (τ (unitOnList S)) ≤ Λ * S.length
  | [], _ => by
      simp [unitOnList]
  | a :: t, h => by
      -- Bound for head
      have hb : Int.natAbs (τ (e a)) ≤ Λ := by
        exact h a (by simp)
      -- Inductive hypothesis for tail
      have ht : ∀ b ∈ t, Int.natAbs (τ (e b)) ≤ Λ := by
        intro b hb'
        exact h b (by simp [hb'])
      have ih := lipschitz_unitOnList t ht
      -- Triangle inequality + arithmetic
      calc
        Int.natAbs (τ (unitOnList (a :: t)))
            = Int.natAbs (τ (unitOnList t + e a)) := by simp [unitOnList]
        _   ≤ Int.natAbs (τ (unitOnList t)) + Int.natAbs (τ (e a)) := by
              -- |τ(x+y)| ≤ |τ x| + |τ y|
              simpa [map_add] using Int.natAbs_add_le (τ (unitOnList t)) (τ (e a))
        _   ≤ Λ * t.length + Λ := by
              exact Nat.add_le_add ih hb
        _   = Λ * (t.length + 1) := by
              -- Λ * t.length + Λ = Λ * (t.length + 1)
              simpa using (Nat.mul_succ Λ t.length).symm
        _   = Λ * (List.length (a :: t)) := by simp

end TauProofs
