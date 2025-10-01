import Spectral.Core
open Spectral

def demoA : Scan := ⟨"A", 1, 163, ⟨1,1,1⟩⟩
def demoB : Scan := ⟨"B", 0, 163, ⟨1,0,1⟩⟩
def demoF : Flow := { source := demoA, target := demoB, intersection := 1 }
def demoCohort : Cohort := { scans := [demoA, demoB], flows := [demoF] }

def main : IO Unit := do
  let json := emitCohortTrace demoCohort
  IO.println json
