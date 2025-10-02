import Spectral.Core
open Spectral

def demoFace : Scan := ⟨"Patient-α", 6, 163, ⟨1,1,1⟩⟩
def faceCohort : Cohort := { scans := [demoFace], flows := [] }

def main : IO Unit := do
  let json := emitCohortTrace faceCohort
  IO.println json
