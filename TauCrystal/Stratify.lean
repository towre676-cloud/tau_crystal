import Std
namespace TauCrystal.Stratify
open Std
structure Stratum where id : Nat; size : Nat deriving Repr, Inhabited
def colimitSize (ss : List Stratum) : Nat := ss.foldl (fun a s => a + s.size) 0
structure CostModel where a : Float; b : Float; cost : Float deriving Repr, Inhabited
def estimateCost (ss : List Stratum) (a : Float := 1.0) (b : Float := 0.05) : CostModel :=
  let n := Float.ofNat (colimitSize ss); let m := Float.ofNat ss.length
  { a := a, b := b, cost := a * n + b * m }
def strataJson (ss : List Stratum) : String :=
  let one (s : Stratum) := s!"{{\"id\":{s.id},\"size\":{s.size}}}"
  "[" ++ String.intercalate "," (ss.map one) ++ "]"
end TauCrystal.Stratify
