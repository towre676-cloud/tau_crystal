import Std
import TauCrystal.Sheaf
import TauCrystal.EconRisk
import TauCrystal.Topology
import TauCrystal.Robust
import TauCrystal.Stratify
import TauCrystal.Edition

open Std

def atD {α} (xs : List α) (i : Nat) (d : α) : α :=
  match xs.get? i with
  | some a => a
  | none   => d

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
  let ps  := TauCrystal.Sheaf.pulse roi
  let risk := TauCrystal.EconRisk.certifyRisk roi
  let bars := TauCrystal.Topology.bars roi 0.0
  let ref  := TauCrystal.Topology.bars ((List.range roi.length).map (fun _ => 0.0)) 0.0
  let life := TauCrystal.Topology.lifetime bars
  let mass := TauCrystal.Topology.mass bars
  let bn   := TauCrystal.Topology.bottleneck bars ref
  let (_rob, sig) := TauCrystal.Robust.stabilize roi 2.5
  let shards : List TauCrystal.Stratify.Stratum :=
    if TauCrystal.Edition.goldFeaturesEnabled then
      [{id := 0, size := 120000}, {id := 1, size := 120000}, {id := 2, size := 100000}]
    else
      [{id := 0, size := 50000}, {id := 1, size := 50000}, {id := 2, size := 40000}]
  let cm := TauCrystal.Stratify.estimateCost shards 1.0 0.05
  -- Čech obstruction
  let cover : TauCrystal.Sheaf.Cover := [(0,"U0"),(1,"U1"),(2,"U2")]
  let insts : List TauCrystal.EconRisk.Instrument :=
    [{ id := 0, name := "U0" }, { id := 1, name := "U1" }, { id := 2, name := "U2" }]
  let lsecs := TauCrystal.EconRisk.roiPresheaf insts (fun i => atD roi i.id 0.0)
  let cech := TauCrystal.Sheaf.assemble cover lsecs 1.0
  let obs  := TauCrystal.Sheaf.obstructionL1 cech
  -- deterministic key
  let key := TauCrystal.Sheaf.fnv1a64 (toString ps ++ toString risk ++ toString bars ++ toString sig ++ toString obs)
  let mani : Manifest := {
    edition       := TauCrystal.Edition.name,
    hash          := key,
    pulses        := TauCrystal.Sheaf.pulsesJson ps,
    risk          := TauCrystal.EconRisk.riskJson risk,
    bars          := TauCrystal.Topology.barsJson bars,
    robust        := TauCrystal.Robust.robustJson sig,
    strata        := TauCrystal.Stratify.strataJson shards,
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
