import Std
namespace TauCrystal.Sheaf
open Std

structure TauPulse where
  k      : Nat
  tau    : Float
  energy : Float
deriving Repr, Inhabited

structure Section where
  chart : Nat
  value : Float
deriving Repr, Inhabited

abbrev Cover := List (Nat × String)

structure CechComplex where
  c0 : List Section
  c1 : List (Nat × Nat × Float)
deriving Repr, Inhabited

-- all unordered pairs (i<j) of a list of Nats
def pairs (xs : List Nat) : List (Nat × Nat) :=
  let rec go : List Nat → List (Nat × Nat)
  | []       => []
  | i :: is  => (is.map (fun j => (i, j))) ++ go is
  go xs

def assemble (_cover : Cover) (locs : List Section) (overlap : Float := 1.0) : CechComplex :=
  let idx   : List Nat := locs.map (fun s => s.chart)
  let edges : List (Nat × Nat) := pairs idx
  let c1    : List (Nat × Nat × Float) :=
    edges.map (fun (i, j) =>
      let vi := (locs.find? (fun s => s.chart = i)).getD { chart := i, value := 0.0 }
      let vj := (locs.find? (fun s => s.chart = j)).getD { chart := j, value := 0.0 }
      (i, j, overlap * (vi.value - vj.value)))
  { c0 := locs, c1 := c1 }

def obstructionL1 (C : CechComplex) : Float :=
  C.c1.foldl (fun acc t => acc + Float.abs t.snd.snd) 0.0

def pulse (xs : List Float) : List TauPulse :=
  let α : Float := 0.33
  let rec go (k : Nat) (e : Float) (τ : Float) (rs : List Float) (out : List TauPulse) :=
    match rs with
    | []      => out.reverse
    | x :: xs =>
      let e' : Float := e * (1.0 - α) + Float.abs x
      let τ' : Float := τ + (Float.abs x) / (1.0 + e')
      go (k+1) e' τ' xs ({ k := k, tau := τ', energy := e' } :: out)
  go 0 0.0 0.0 xs []

def fnv1a64 (s : String) : String :=
  let off   : UInt64 := 0xcbf29ce484222325
  let prime : UInt64 := 0x00000100000001B3
  let h := s.foldl (init := off) (fun h c => (h ^^^ (UInt64.ofNat c.toNat)) * prime)
  toString h

def pulseJson (p : TauPulse) : String :=
  s!"{{\"k\":{p.k},\"tau\":{p.tau},\"energy\":{p.energy}}}"

def pulsesJson (ps : List TauPulse) : String :=
  "[" ++ String.intercalate "," (ps.map pulseJson) ++ "]"

end TauCrystal.Sheaf
