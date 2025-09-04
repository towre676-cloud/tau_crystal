import Std
import TauCrystal
import TauCrystal.Sheaf
import TauCrystal.EconRisk
import TauCrystal.Topology
import TauCrystal.Robust
import TauCrystal.Stratify
import TauCrystal.Edition

open Std
open TauCrystal

structure Manifest where
  edition       : String
  hash          : String
  pulses        : String
  risk          : String
  bars          : String
  robust        : String
  strata        : String
  lifetime      : Nat
  mass          : Float
  bottleneck    : Float
  obstructionL1 : Float
  cost          : Float
deriving Repr

def manifestJson (m : Manifest) : String :=
  s!"{{\"edition\":\"{m.edition}\",\"hash\":\"{m.hash}\",\"pulses\":{m.pulses},\"risk\":{m.risk},\"bars\":{m.bars},\"robust\":{m.robust},\"strata\":{m.strata},\"lifetime\":{m.lifetime},\"mass\":{m.mass},\"bottleneck\":{m.bottleneck},\"obstructionL1\":{m.obstructionL1},\"cost\":{m.cost}}}"

def demoROI : List Float :=
  let base := (List.range 60).map (fun i => 0.01 * Float.sin (Float.ofNat i / 3.0))
  let shock := (List.range 40).map (fun i => 0.02 * Float.sin (Float.ofNat i / 2.0) + 0.03)
  base ++ shock

def main : IO Unit := do
  let roi := demoROI
  let ps  := Sheaf.pulse roi
  let risk := EconRisk.certifyRisk roi
  let bars := Topology.bars roi 0.0
  let ref  := Topology.bars ((List.range roi.length).map (fun _ => 0.0)) 0.0
  let life := Topology.lifetime bars
  let mass := Topology.mass bars
  let bn   := Topology.bottleneck bars ref
  let (rob, sig) := Robust.stabilize roi 2.5
  let shards : List Stratify.Stratum :=
    if TauCrystal.Edition.goldFeaturesEnabled then
      [{id:=0, size:=120000},{id:=1, size:=120000},{id:=2, size:=100000}]
    else
      [{id:=0, size:=50000},{id:=1, size:=50000},{id:=2, size:=40000}]
  let cm := Stratify.estimateCost shards 1.0 0.05
  -- Build a tiny cover and compute Čech obstruction from ROI-as-sections
  let cover : Sheaf.Cover := [(0,"U0"),(1,"U1"),(2,"U2")]
  let insts := [{EconRisk.Instrument.mk 0 "U0"},
                {EconRisk.Instrument.mk 1 "U1"},
                {EconRisk.Instrument.mk 2 "U2"}]
  let lsecs := EconRisk.roiPresheaf insts (fun i =>
                  let idx := i.id
                  let x := roi.getD idx 0.0
                  x)
  let cech := Sheaf.assemble cover lsecs 1.0
  let obs := Sheaf.obstructionL1 cech
  -- Deterministic internal key
  let key := Sheaf.fnv1a64 (toString ps ++ toString risk ++ toString bars ++ toString sig ++ toString obs)
  let mani : Manifest := {
    edition       := TauCrystal.Edition.name,
    hash          := key,
    pulses        := Sheaf.pulsesJson ps,
    risk          := EconRisk.riskJson risk,
    bars          := Topology.barsJson bars,
    robust        := Robust.robustJson sig,
    strata        := Stratify.strataJson shards,
    lifetime      := life,
    mass          := mass,
    bottleneck    := bn,
    obstructionL1 := obs,
    cost          := cm.cost
  }
  let js := manifestJson mani
  IO.FS.createDirAll "manifests"
  IO.FS.writeFile "manifests/tau_fusion.json" js
  IO.println s!"wrote manifests/tau_fusion.json (edition={mani.edition}, key={key})"
