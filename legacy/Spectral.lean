import Std

namespace TauCrystal

abbrev F := Float
abbrev Vec := Array F

private def mkVec (n : Nat) (f : Nat → F) : Vec :=
  Id.run do
    let mut a := Array.replicate n 0.0
    for i in [:n] do
      a := a.set! i (f i)
    a

private def vlin (a : F) (x : Vec) (b : F) (y : Vec) : Vec :=
  Id.run do
    let n := x.size
    let mut out := Array.replicate n 0.0
    for i in [:n] do
      out := out.set! i (a * x[i]! + b * y[i]!)
    out

/-- Burn deterministic floating ops roughly linear in `reps`. -/
def burn (reps : Nat) : IO Unit := do
  let n : Nat := 8192
  let x : Vec := mkVec n (fun i => (Float.ofNat (i + 1)) / (Float.ofNat (n + 1)))
  let mut t0 := x
  let mut t1 := x.map (fun v => v - 0.5)
  let iters : Nat := 12
  let mut checksum : F := 0.0
  for _ in [:reps] do
    let mut a0 := t0
    let mut a1 := t1
    for _ in [:iters] do
      let a2 := vlin 2.0 a1 (-1.0) a0
      a0 := a1
      a1 := a2
    checksum := checksum + a1[0]! + a1[n / 2]! + a1[n - 1]!
    t0 := t1
    t1 := a1
  if checksum == 42.4242 then
    IO.println "never happens"
  pure ()

end TauCrystal
