import Mathlib.GroupTheory.FreeAbelianGroup
import Mathlib.Data.List.Basic

namespace TauProofs

variable {α β γ : Type*}

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

/-- Composition of pushforwards is pushforward of composition. -/
lemma pushforward_comp (φ : α → β) (ψ : β → γ) :
    (pushforward ψ).comp (pushforward φ) = pushforward (ψ ∘ φ) := by
  -- ext on the free abelian group basis
  ext a; simp [pushforward_on_basis, Function.comp]

end TauProofs
