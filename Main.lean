import TauCrystal.Core
import Receipt.Receipt

def main : IO Unit := do
  IO.println TauCrystal.hello
  if Receipt.isCanonical "stub" then
    IO.println "✅ app: PASSED"
  else
    IO.println "❌ app: FAILED"
