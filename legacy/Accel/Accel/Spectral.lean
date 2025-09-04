import Batteries

namespace TauCrystal.Accel

def chebDegree (ds : Float) (eps : Float) : Nat :=
  let ds'  := if ds <= 0.0 then 1.0 else ds
  let eps' := if eps <= 0.0 then 1e-6 else eps
  let m    := (ds' * Float.log (1.0/eps')).ceil.toNat
  Nat.max m 4

/-- Placeholder: prints chosen Chebyshev degree; drop SpMV/Krylov here. -/
def runSpectral (ds eps : Float) : IO Unit := do
  let m := chebDegree ds eps
  IO.println s!"accel: spectral ds={ds} eps={eps} m={m}"
  pure ()
