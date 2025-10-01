namespace Spectral

-- TODO: wire these to your real modules when ready:
-- import Spectral.Kernel.Emit
-- import Spectral.Kernel.Types
-- import Spectral.Kernel.Invariants

structure Scan where
  label     : String
  baseAngle : Int
  p         : Int
  symmetry  : Int × Int × Int
  deriving DecidableEq

structure Flow where
  source       : Scan
  target       : Scan
  intersection : Int
  deriving DecidableEq

structure Cohort where
  scans : List Scan
  flows : List Flow
  deriving DecidableEq

-- The following assume your kernel provides these names:
--   Box, Edge, emitNode, emitEdge, emitPlumbingTrace, tamagawa, boxMaslov, globalMaslov

def scanMaslov (s : Scan) : Int := boxMaslov {
  label   := s.label
  framing := s.baseAngle
  p       := s.p
  heegner := s.symmetry
}

def strain (s : Scan) : Nat := tamagawa (-163) s.p

def globalSymmetry (C : Cohort) : Int := globalMaslov {
  vertices := C.scans.map (fun s => Box.mk s.label s.baseAngle s.p s.symmetry)
  edges    := C.flows.map (fun f => Edge.mk
                          (Box.mk f.source.label f.source.baseAngle f.source.p f.source.symmetry)
                          (Box.mk f.target.label f.target.baseAngle f.target.p f.target.symmetry)
                          f.intersection)
}

def emitScan (s : Scan) : String :=
  emitNode (Box.mk s.label s.baseAngle s.p s.symmetry) (-163)

def emitFlow (f : Flow) : String :=
  emitEdge (Edge.mk
    (Box.mk f.source.label f.source.baseAngle f.source.p f.source.symmetry)
    (Box.mk f.target.label f.target.baseAngle f.target.p f.target.symmetry)
    f.intersection)

def emitCohortTrace (C : Cohort) : String :=
  emitPlumbingTrace (-163) {
    vertices := C.scans.map (fun s => Box.mk s.label s.baseAngle s.p s.symmetry)
    edges    := C.flows.map (fun f => Edge.mk
      (Box.mk f.source.label f.source.baseAngle f.source.p f.source.symmetry)
      (Box.mk f.target.label f.target.baseAngle f.target.p f.target.symmetry)
      f.intersection)
  }

end Spectral
