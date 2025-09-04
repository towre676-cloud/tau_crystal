import Std
namespace TauCrystal.Sheaf
open Std
structure TauPulse where k : Nat; tau : Float; energy : Float deriving Repr, Inhabited
structure Section  where chart : Nat; value : Float deriving Repr, Inhabited
abbrev Cover := List (Nat × String)
structure CechComplex where c0 : List Section; c1 : List (Nat × Nat × Float) deriving Repr, Inhabited
def assemble (_ : Cover) (locs : List Section) (overlap : Float := 1.0) : CechComplex :=
  let idx := locs.map (·.chart)
  let pairs := (List.sigma idx (fun i => idx)).filter (fun p => p.fst < p.snd) |>.map (fun p => (p.fst,p.snd))
  let c1 := pairs.map (fun (i,j) =>
    let vi := (locs.find? (fun s => s.chart = i)).getD {chart:=i, value:=0.0}
    let vj := (locs.find? (fun s => s.chart = j)).getD {chart:=j, value:=0.0}
    (i,j, overlap * (vi.value - vj.value)))
  { c0 := locs, c1 := c1 }
def obstructionL1 (C : CechComplex) : Float := C.c1.foldl (fun a t => a + Float.abs t.snd.snd) 0.0
def pulse (xs : List Float) : List TauPulse :=
  let α : Float := 0.33
  let rec go (k : Nat) (e τ : Float) (rs : List Float) (out : List TauPulse) :=
    match rs with
    | [] => out.reverse
    | x::xs =>
      let e' := e * (1.0 - α) + Float.abs x
      let τ' := τ + (Float.abs x) / (1.0 + e')
      go (k+1) e' τ' xs ({k:=k, tau:=τ', energy:=e'} :: out)
  go 0 0.0 0.0 xs []
def fnv1a64 (s : String) : String :=
  let off : UInt64 := 0xcbf29ce484222325; let prime : UInt64 := 0x00000100000001B3
  toString <| s.foldl (init := off) (fun h c => (h ^^^ (UInt64.ofNat c.toNat)) * prime)
def pulseJson (p : TauPulse) : String := s!"{{\"k\":{p.k},\"tau\":{p.tau},\"energy\":{p.energy}}}"
def pulsesJson (ps : List TauPulse) : String := "[" ++ String.intercalate "," (ps.map pulseJson) ++ "]"
end TauCrystal.Sheaf
