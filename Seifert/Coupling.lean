import Std
import Tau.WeightedFlow
import Residue.ConstraintCohomology
namespace Seifert
open Tau Residue
/-- lcm over a list (1 as neutral). -/
def lcmList (xs : List Nat) : Nat := xs.foldl Nat.lcm 1
/-- Seifert index n := lcm of exceptional fiber orders. -/
def seifertIndex (a : List Nat) : Nat := lcmList a
/-- Weight W := |e| as a simple nonnegative lift of Euler class. -/
def weight (e : Rat) : Rat := if e < 0 then -e else e
/-- τ‑pulse from Seifert data: τ = ω(n) · kinetic. -/
def tauFromSeifert (a : List Nat) (kinetic : Rat) : Rat :=
  let n := seifertIndex a; tauPulse n kinetic
/-- ΔE(1→n; W(e)) discrete surrogate with constant weight W. -/
def deltaEFromSeifert (a : List Nat) (e : Rat) : Rat :=
  let n := seifertIndex a
  let W : Nat → Rat := fun _ => weight e
  Residue.deltaE 1 n W
/-- A sample Γ pulse between n and the largest aᵢ (as a coarse boundary stress). -/
def gammaSample (a : List Nat) : Rat :=
  match a with
  | []      => 0
  | xs      =>
    let n := seifertIndex xs
    let m := xs.foldl Nat.max 1
    Residue.gammaPulse n m
end Seifert
