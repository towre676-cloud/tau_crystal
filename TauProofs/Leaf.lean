import Mathlib.GroupTheory.FreeAbelianGroup
import Mathlib.Data.List.Basic

namespace TauProofs

variable {α β γ : Type*}

@[simp] def e (a : α) : FreeAbelianGroup α :=
  FreeAbelianGroup.of a

/-- Sum of basis vectors over a list (recursive, no BigOperators). -/
def unitOnList : List α → FreeAbelianGroup α
| []      => 0
| a :: t  => unitOnList t + e a

def pushforward (φ : α → β) : FreeAbelianGroup α →+ FreeAbelianGroup β :=
  FreeAbelianGroup.lift (fun a => e (φ a))

@[simp] lemma pushforward_on_basis (φ : α → β) (a : α) :
  pushforward φ (e a) = e (φ a) := rfl

/-- Composition of pushforwards is pushforward of composition. -/
lemma pushforward_comp (φ : α → β) (ψ : β → γ) :
    (pushforward ψ).comp (pushforward φ) = pushforward (ψ ∘ φ) := by
  ext a
  -- Unfold pushforward to lifts; then `lift_of` twice, on both sides.
  simp [pushforward, Function.comp]

/-- Delta on lists. -/
def deltaList (φ : α → β) (Src : List α) (Dst : List β) : FreeAbelianGroup β :=
  (pushforward φ) (unitOnList Src) - unitOnList Dst

end TauProofs
