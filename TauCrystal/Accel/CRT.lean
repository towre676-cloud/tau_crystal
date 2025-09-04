import Batteries

namespace TauCrystal.Accel

def parsePrimes (s : String) : List Nat :=
  s.split (· = ',') |>.map (·.trim) |>.filter (· ≠ "")
   |>.map (fun t => match t.toNat? with | some n => n | none => 0)
   |>.filter (· ≠ 0)

/-- Placeholder: echoes chosen primes; wire real mod-p shards later. -/
def runCRT (primes : List Nat) (obstructionDim : Int) : IO Unit := do
  let shown := String.intercalate ", " (primes.map (·.toString))
  IO.println s!"accel: crt primes=[{shown}]"
  pure ()
