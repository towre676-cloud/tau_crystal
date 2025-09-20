import Tau.LeafGroup
namespace Tau

structure LeafMorphism where
  srcSupport : List LeafID
  dstSupport : List LeafID
  map        : LeafID → LeafID

def unitOn (xs : List LeafID) : LeafGroup :=
  fun x => if x ∈ xs then 1 else 0

def applyMorphism (phi : LeafMorphism) (f : LeafGroup) : LeafGroup :=
  fun y => phi.srcSupport.foldl (fun acc x => if phi.map x = y then acc + f x else acc) 0

def computeDelta (phi : LeafMorphism) : LeafGroup :=
  applyMorphism phi (unitOn phi.srcSupport) + (- unitOn phi.dstSupport)

structure TauFunctional where
  eval : LeafGroup → Int

def tauDrift (phi : LeafMorphism) (tau : TauFunctional) (src dst : LeafGroup) : Int :=
  let push := applyMorphism phi src
  tau.eval dst - tau.eval push

def verifyObstruction (lam : Nat) (tau : TauFunctional)
  (phi : LeafMorphism) (src dst : LeafGroup) : Bool × String :=
  let delta : LeafGroup := computeDelta phi
  let l1    : Nat       := leafGroupL1Norm delta phi.dstSupport
  let drift : Int       := tauDrift phi tau src dst
  let ok :=
    if l1 = 0 then (drift = 0)
    else (Int.natAbs drift ≤ lam * l1)
  if ok then
    if l1 = 0 then (true, "VERIFIED: DELTA=0, tau conserved")
    else            (true, "VERIFIED: |dTau| <= lambda * L1")
  else
    (false, "FAILED: |dTau| > lambda * L1")

end Tau
