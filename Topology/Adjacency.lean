import Std
import Tau.WeightedFlow
namespace Topology
open Tau
def Rentry (i j : Nat) : Rat :=
  if i = 0 ∨ j = 0 then 0 else
    let g := Tau.gcd i j
    if g ≤ 1 then 0 else (Tau.phi g : Rat) / (Nat.max i j : Rat)
def Rmatrix (n : Nat) : Array (Array Rat) :=
  Array.tabulate (n+1) (fun i => Array.tabulate (n+1) (fun j => Rentry i j))
def frob (n : Nat) : Rat :=
  let mut s : Rat := 0
  for i in [1:n+1] do for j in [1:n+1] do let x := Rentry i j; s := s + x * x
  s
end Topology
