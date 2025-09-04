import Std
namespace TauCrystal.Robust
open Std

def clamp (x lo hi : Float) : Float :=
  if x < lo then lo else if x > hi then hi else x

structure RobustSig where
  mean    : Float
  std     : Float
  tails   : Nat
  clipped : Nat
deriving Repr, Inhabited

def meanStd (xs : List Float) : Float × Float :=
  if xs.isEmpty then (0.0, 0.0) else
    let n := Float.ofNat xs.length
    let μ := xs.foldl (· + ·) 0.0 / n
    let σ := Float.sqrt ((xs.foldl (fun a x => a + (x - μ) * (x - μ)) 0.0) / n)
    (μ, σ)

def stabilize (xs : List Float) (k : Float := 3.0) : (List Float) × RobustSig :=
  if xs.isEmpty then ([], {mean := 0.0, std := 0.0, tails := 0, clipped := 0}) else
    let (μ, σ) := meanStd xs
    let denom := if σ == 0.0 then 1.0 else σ
    let rec f (rs : List Float) (out : List Float) (tails clipped : Nat) :=
      match rs with
      | [] => (out.reverse, {mean := μ, std := σ, tails := tails, clipped := clipped})
      | x :: xs =>
        let z := (x - μ) / denom
        let tails' := if Float.abs z > k then tails + 1 else tails
        let zc := clamp z (-k) k
        let clipped' := if zc != z then clipped + 1 else clipped
        f xs (zc :: out) tails' clipped'
    f xs [] 0 0

def robustJson (r : RobustSig) : String :=
  s!"{{\"mean\":{r.mean},\"std\":{r.std},\"tails\":{r.tails},\"clipped\":{r.clipped}}}"

end TauCrystal.Robust
