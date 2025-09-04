import Std

namespace TauCrystal.Topology

open Std

structure Bar where
  birth  : Nat
  death  : Nat
  height : Float
deriving Repr, Inhabited

def bars (xs : List Float) (θ : Float := 0.0) : List Bar :=
  let rec go (i : Nat) (open? : Bool) (b : Nat) (hmax : Float) (rest : List Float) (out : List Bar) :=
    match rest with
    | [] =>
      if open? then {birth := b, death := i, height := hmax} :: out |>.reverse else out.reverse
    | x :: rs =>
      let above := x > θ
      match open?, above with
      | false, false => go (i+1) false b hmax rs out
      | false, true  => go (i+1) true  i x    rs out
      | true,  true  => go (i+1) true  b (Float.max hmax x) rs out
      | true,  false => go (i+1) false b hmax rs ({birth := b, death := i, height := hmax} :: out)
  go 0 false 0 0.0 xs []

def lifetime (bs : List Bar) : Nat :=
  bs.foldl (fun acc b => acc + (b.death - b.birth)) 0

def mass (bs : List Bar) : Float :=
  bs.foldl (fun acc b => acc + (Float.ofNat (b.death - b.birth)) * b.height) 0.0

def bottleneck (a b : List Bar) : Float :=
  let n := Nat.min a.length b.length
  let pairs := (List.range n).map (fun i => (a.get! i, b.get! i))
  pairs.foldl (fun acc ⟨x,y⟩ =>
    let la := Float.ofNat (x.death - x.birth)
    let lb := Float.ofNat (y.death - y.birth)
    Float.max acc (Float.abs (la - lb))) 0.0

def barJson (b : Bar) : String :=
  s!"{{\"birth\":{b.birth},\"death\":{b.death},\"height\":{b.height}}}"

def barsJson (bs : List Bar) : String :=
  "[" ++ String.intercalate "," (bs.map barJson) ++ "]"

end TauCrystal.Topology
