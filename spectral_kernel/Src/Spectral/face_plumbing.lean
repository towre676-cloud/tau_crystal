import Spectral.Plumbing

namespace Face

/-- 1. Facial analogue of a Heegner box ----------------------------- -/
structure Scan where
  label      : String   -- patient ID or region
  baseAngle  : ℤ        -- mandibular projection / “framing”
  p          : ℕ        -- prime of *anatomical* reduction (here: landmark index)
  symmetry   : QuadK (-163)  -- dummy CM field; carries parity bit
  deriving DecidableEq

def scanMaslov (s : Scan) : ℤ := boxMaslov {
  label   := s.label
  framing := s.baseAngle
  p       := s.p
  heegner := s.symmetry
}

/-- 2. Local tissue discrepancy ----------------------------------- -/
def strain (s : Scan) : ℕ := tamagawa (-163) s.p

/-- 3. Morphological flow edge ------------------------------------ -/
structure Flow where
  source      : Scan
  target      : Scan
  intersection : ℤ  -- geometric flow magnitude (mm or PCA units)
  deriving DecidableEq

/-- 4. Cohort = plumbing graph ------------------------------------ -/
structure Cohort where
  scans : List Scan
  flows : List Flow
  deriving DecidableEq

def globalSymmetry (C : Cohort) : ℤ := globalMaslov {
  vertices := C.scans.map (fun s => Box.mk s.label s.baseAngle s.p s.symmetry)
  edges    := C.flows.map (fun f => Edge.mk
                                 (Box.mk f.source.label f.source.baseAngle f.source.p f.source.symmetry)
                                 (Box.mk f.target.label f.target.baseAngle f.target.p f.target.symmetry)
                                 f.intersection)
}

/-- 5. JSON emitter (re-use kernel printer) ----------------------- -/
def emitScan (s : Scan) : String := emitNode (Box.mk s.label s.baseAngle s.p s.symmetry) (-163)
def emitFlow (f : Flow) : String := emitEdge (Edge.mk
                                 (Box.mk f.source.label f.source.baseAngle f.source.p f.source.symmetry)
                                 (Box.mk f.target.label f.target.baseAngle f.target.p f.target.symmetry)
                                 f.intersection)

def emitCohortTrace (C : Cohort) : String := emitPlumbingTrace (-163) {
  vertices := C.scans.map (fun s => Box.mk s.label s.baseAngle s.p s.symmetry)
  edges    := C.flows.map (fun f => Edge.mk
                                 (Box.mk f.source.label f.source.baseAngle f.source.p f.source.symmetry)
                                 (Box.mk f.target.label f.target.baseAngle f.target.p f.target.symmetry)
                                 f.intersection)
}

/-- 6. Demo: the same trefoil data, now a *face* ------------------ -/
def demoFace : Scan := ⟨"Patient-α", 6, 163, ⟨1,1,1⟩⟩
def demoCohort : Cohort := { scans := [demoFace], flows := [] }

#eval emitCohortTrace demoCohort

end Face

-- add a second face and a flow edge (phase flip demo)
def demoFace2 : Scan := ⟨"Patient-β", 7, 163, ⟨1,1,1⟩⟩
def demoFlow  : Flow := { source := demoFace, target := demoFace2, intersection := 1 }
-- replace single-node cohort with two scans + one flow
def demoCohort : Cohort := { scans := [demoFace, demoFace2], flows := [demoFlow] }

#eval emitCohortTrace demoCohort
