import Tau.LeafGroup
namespace Tau

structure LeafMorphism where
  srcSupport : List LeafID
  dstSupport : List LeafID
  map        : LeafID → LeafID
  -- In this minimal build we do not enforce membership proofs.

def unitOn (xs : List LeafID) : LeafGroup :=
  fun x => if x ∈ xs then 1 else 0

def applyMorphism (φ : LeafMorphism) (f : LeafGroup) : LeafGroup :=
  fun y => φ.srcSupport.foldl (fun acc x => if φ.map x = y then acc + f x else acc) 0

def computeDelta (φ : LeafMorphism) : LeafGroup :=
  applyMorphism φ (unitOn φ.srcSupport) + (- unitOn φ.dstSupport)

structure TauFunctional where
  eval     : LeafGroup → Int
  additive : Bool := true  -- placeholder flag; pure-IO build doesn’t depend on it

def tauDrift (φ : LeafMorphism) (τ : TauFunctional) (src dst : LeafGroup) : Int :=
  let push := applyMorphism φ src
  τ.eval dst - τ.eval push

def verifyObstruction (λb : Nat) (τ : TauFunctional)
  (φ : LeafMorphism) (src dst : LeafGroup) : Bool × String :=
  let δ    := computeDelta φ
  let δ₁   := leafGroupL1Norm δ φ.dstSupport
  let drift := tauDrift φ τ src dst
  let ok :=
    if δ₁ = 0 then (drift = 0)
    else (Int.natAbs drift ≤ λb * δ₁)
  if ok then
    if δ₁ = 0 then (true, "VERIFIED: Δ=0, τ conserved")
    else (true, "VERIFIED: |Δτ| ≤ λ‖Δ‖₁")
  else
    (false, "FAILED: |Δτ| > λ‖Δ‖₁")

end Tau
