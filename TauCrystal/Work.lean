import TauCrystal
import TauCrystal.Spectral

namespace TauCrystal

def runWithBurn (argv : List String) : IO UInt32 := do
  let reps := match (← IO.getEnv "TC_WORK_REPS") with
    | some s => (String.toNat? s).getD 1
    | none   => 1
  if reps > 1 then
    (TauCrystal.burn reps)
  run argv

end TauCrystal
