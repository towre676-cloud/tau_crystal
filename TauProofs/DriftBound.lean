import Mathlib.Algebra.FreeAbelianGroup
import Mathlib.Data.Int.Basic
import Mathlib.Data.List.Basic
import TauProofs.TauBounds

namespace TauProofs
open FreeAbelianGroup

/-- A symbolic certificate that a unit-sum delta over a list `S`
    satisfies the τ-drift Lipschitz bound with constant `Λ`. -/
structure DriftCertificate (β : Type*) where
  S        : List β
  Λ        : Nat
  τ        : TauFunctional β
  perBound : ∀ b ∈ S, Int.natAbs (τ (of b)) ≤ Λ
  bound    : Int.natAbs (τ (unitFromList S)) ≤ Λ * S.length

/-- Build a `DriftCertificate` directly from pointwise bounds using
    the Lipschitz lemma over lists. -/
def DriftCertificate.mkFromList
  {β : Type*} (τ : TauFunctional β) (Λ : Nat)
  (S : List β) (h : ∀ b ∈ S, Int.natAbs (τ (of b)) ≤ Λ) :
  DriftCertificate β :=
  {
    S := S
  , Λ := Λ
  , τ := τ
  , perBound := h
  , bound := by
      -- Reuse the proven Lipschitz inequality.
      simpa using lipschitz_unitFromList (β:=β) τ Λ S h
  }

end TauProofs
