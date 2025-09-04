import Batteries

namespace TauCrystal.Accel

/-- Placeholder: signals quasi-linear tree layout; hook real tiling later. -/
def runHyperbolic (n : Nat) : IO Unit := do
  IO.println s!"accel: hyperbolic n={n} layout=tree quasi_linear"
  pure ()
