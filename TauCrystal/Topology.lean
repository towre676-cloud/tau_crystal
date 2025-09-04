import Std
namespace TauCrystal.Topology
open Std
def fmax (a b : Float) : Float := if a < b then b else a
structure Bar where birth : Nat; death : Nat; height : Float deriving Repr, Inhabited
def bars (xs : List Float) (θ : Float := 0.0) : List Bar :=
  let rec go (i : Nat) (openp : Bool) (b : Nat) (hmax : Float) (rs : List Float) (out : List Bar) :=
    match rs with
    | [] => if openp then ({birth:=b, death:=i, height:=hmax} :: out).reverse else out.reverse
    | x::xs =>
      let above := x > θ
      if !openp && !above then go (i+1) false b hmax xs out
      else if !openp && above then go (i+1) true i x xs out
      else if openp && above then go (i+1) true b (fmax hmax x) xs out
      else go (i+1) false b hmax xs ({birth:=b, death:=i, height:=hmax} :: out)
  go 0 false 0 0.0 xs []
def lifetime (bs : List Bar) : Nat := bs.foldl (fun a b => a + (b.death - b.birth)) 0
def mass (bs : List Bar) : Float := bs.foldl (fun a b => a + (Float.ofNat (b.death - b.birth)) * b.height) 0.0
def bottleneck (a b : List Bar) : Float :=
  let n := Nat.min a.length b.length
  let pairs := (List.range n).map (fun i => (a[i]!, b[i]!))
  pairs.foldl (fun acc (x,y) =>
    let la := Float.ofNat (x.death - x.birth); let lb := Float.ofNat (y.death - y.birth)
    let d := Float.abs (la - lb); if acc < d then d else acc) 0.0
def barJson (b : Bar) : String := s!"{{\"birth\":{b.birth},\"death\":{b.death},\"height\":{b.height}}}"
def barsJson (bs : List Bar) : String := "[" ++ String.intercalate "," (bs.map barJson) ++ "]"
end TauCrystal.Topology
