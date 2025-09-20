/-! Core imports & small helpers for FreeAbelianGroup over leaves. -/
import Mathlib.GroupTheory.FreeAbelianGroup
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.GroupWithZero.Power

namespace TauProofs

open scoped BigOperators

/-- A leaf label; keep abstract, we supply finite supports as `Finset`. -/
variable {α β γ : Type _}

/-- Basis vector in the free abelian group. -/
@[simp] def e (a : α) : FreeAbelianGroup α := FreeAbelianGroup.of a

/-- Unit on a finite support. -/
def unitOn (S : Finset α) : FreeAbelianGroup α :=
  ∑ a in S, e a

/-- Pushforward of coefficients along a function. -/
def pushforward (φ : α → β) : FreeAbelianGroup α →+ FreeAbelianGroup β :=
  FreeAbelianGroup.lift (fun a => e (φ a))

@[simp] lemma pushforward_on_basis (φ : α → β) (a : α) :
    pushforward φ (e a) = e (φ a) := rfl

/-- Cohomology-style delta: φ₊(1_src) - 1_dst. -/
def delta (φ : α → β) (Src : Finset α) (Dst : Finset β) : FreeAbelianGroup β :=
  (pushforward φ) (unitOn Src) - unitOn Dst

end TauProofs
