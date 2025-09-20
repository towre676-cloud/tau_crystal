import Mathlib.GroupTheory.FreeAbelianGroup
import Mathlib.Data.Finset.Basic

namespace TauProofs

open scoped BigOperators

variable {α β : Type _}

@[simp] def e (a : α) : FreeAbelianGroup α := FreeAbelianGroup.of a

def unitOn (S : Finset α) : FreeAbelianGroup α :=
  ∑ a in S, e a

def pushforward (φ : α → β) : FreeAbelianGroup α →+ FreeAbelianGroup β :=
  FreeAbelianGroup.lift (fun a => e (φ a))

@[simp] lemma pushforward_on_basis (φ : α → β) (a : α) :
  pushforward φ (e a) = e (φ a) := rfl

def delta (φ : α → β) (Src : Finset α) (Dst : Finset β) : FreeAbelianGroup β :=
  (pushforward φ) (unitOn Src) - unitOn Dst

end TauProofs
