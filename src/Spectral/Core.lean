import Spectral.Kernel.Minimal
namespace Spectral

open Spectral.Kernel

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

def scanMaslov (s : Scan) : Int :=
  boxMaslov { label := s.label, framing := s.baseAngle, p := s.p, heegner := s.symmetry }

def strain (s : Scan) : Nat :=
  tamagawa (-163) s.p

def globalSymmetry (C : Cohort) : Int :=
  globalMaslov {
    vertices := C.scans.map (fun s => Spectral.Kernel.Box.mk s.label s.baseAngle s.p s.symmetry)
    edges    := C.flows.map (fun f => Spectral.Kernel.Edge.mk
      (Spectral.Kernel.Box.mk f.source.label f.source.baseAngle f.source.p f.source.symmetry)
      (Spectral.Kernel.Box.mk f.target.label f.target.baseAngle f.target.p f.target.symmetry)
      f.intersection)
  }

def emitScan (s : Scan) : String :=
  emitNode (Spectral.Kernel.Box.mk s.label s.baseAngle s.p s.symmetry) (-163)

def emitFlow (f : Flow) : String :=
  emitEdge (Spectral.Kernel.Edge.mk
    (Spectral.Kernel.Box.mk f.source.label f.source.baseAngle f.source.p f.source.symmetry)
    (Spectral.Kernel.Box.mk f.target.label f.target.baseAngle f.target.p f.target.symmetry)
    f.intersection)

def emitCohortTrace (C : Cohort) : String :=
  emitPlumbingTrace (-163) {
    vertices := C.scans.map (fun s => Spectral.Kernel.Box.mk s.label s.baseAngle s.p s.symmetry)
    edges    := C.flows.map (fun f => Spectral.Kernel.Edge.mk
      (Spectral.Kernel.Box.mk f.source.label f.source.baseAngle f.source.p f.source.symmetry)
      (Spectral.Kernel.Box.mk f.target.label f.target.baseAngle f.target.p f.target.symmetry)
      f.intersection)
  }

end Spectral
