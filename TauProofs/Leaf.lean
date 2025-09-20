import Mathlib.GroupTheory.FreeAbelianGroup
import Mathlib.Data.List.Basic

namespace TauProofs

variable {α β : Type*}

@[simp] def e (a : α) : FreeAbelianGroup α :=
  FreeAbelianGroup.of a

def unitOnList (L : List α) : FreeAbelianGroup α :=
  L.foldl (fun acc a => acc + e a) 0

def pushforward (φ : α → β) : FreeAbelianGroup α →+ FreeAbelianGroup β :=
  FreeAbelianGroup.lift (fun a => e (φ a))

@[simp] lemma pushforward_on_basis (φ : α → β) (a : α) :
  pushforward φ (e a) = e (φ a) := rfl

def deltaList (φ : α → β) (Src : List α) (Dst : List β) : FreeAbelianGroup β :=
  (pushforward φ) (unitOnList Src) - unitOnList Dst

end TauProofs
