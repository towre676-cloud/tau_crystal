import Std
import Tau.WeightedFlow
namespace Residue
open Tau
def Pi (m i : Nat) : Int := if Nat.gcd i m = 1 then 1 else 0
def exclusiveRank (m N : Nat) : Nat :=
  (List.range (N+1)).foldl (fun acc i => acc + (if Pi m i = 1 then 1 else 0)) 0
def lcm (a b : Nat) : Nat := Nat.lcm a b
def gammaPulse (i j : Nat) (gamma0 : Rat := 1) : Rat :=
  if i = 0 ∨ j = 0 then 0 else
    let g := Nat.gcd i j; let L := lcm i j
    if g = 0 ∨ L = 0 then 0 else
      let num := (g : Rat) * (Tau.sigma g : Rat)
      let den := (L : Rat) * (Tau.phi g : Rat)
      if den = 0 then 0 else gamma0 * num / den
def deltaE (n1 n2 : Nat) (W : Nat → Rat := fun _ => 1) : Rat :=
  if n2 ≤ n1 then 0 else
    let rec sum (k : Nat) (acc : Rat) : Rat :=
      if k > n2 then acc else
        let s := Tau.sigma k; let p := Tau.phi k
        let term := if p = 0 then 0 else ((s : Rat) / (p : Rat) - 1) * W k
        sum (k+1) (acc + term)
    sum (n1+1) 0
end Residue
