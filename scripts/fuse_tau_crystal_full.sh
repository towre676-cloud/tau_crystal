#!/usr/bin/env bash
set -euo pipefail

# ---- repo + lake sanity
git rev-parse --is-inside-work-tree >/dev/null 2>&1 || { echo "Not in a git repo"; exit 1; }
test -f lakefile.lean || { echo "lakefile.lean not found (run from project root)"; exit 1; }
test -f Main.lean || { echo "Main.lean not found (run from project root)"; exit 1; }

BRANCH="feature/tau-crystal-fusion-full"
git fetch -q || true
if git show-ref --verify --quiet "refs/heads/$BRANCH"; then
  git checkout "$BRANCH"
else
  git checkout -b "$BRANCH"
fi

mkdir -p TauCrystal manifests

# ===================== LEAN CODE (FULL IMPLEMENTATIONS) =====================

# --- τ Sheaf + Cech obstruction + simple FNV1a hash for deterministic attestation
cat > TauCrystal/Sheaf.lean <<'LEAN'
import Std

namespace TauCrystal.Sheaf

open Std

/-- Algebraic τ-clock and section types. -/
structure TauPulse where
  k     : Nat
  tau   : Float
  energy : Float
deriving Repr, Inhabited

structure Section where
  chart : Nat
  value : Float
deriving Repr, Inhabited

abbrev Cover := List (Nat × String)

/-- Čech 0- and 1-cochains over a finite cover, encoded as lists. -/
structure CechComplex where
  c0 : List Section
  c1 : List (Nat × Nat × Float)  -- pair of charts with a mismatch scalar
deriving Repr, Inhabited

/-- Assemble a Čech complex from local readings, using pairwise overlaps to compute 1-cochains. -/
def assemble (cover : Cover) (local : List Section) (overlap : Float := 1.0) : CechComplex :=
  let idx := local.map (·.chart)
  let pairs :=
    (List.sigma idx (fun i => idx)).filter (fun ⟨i,j⟩ => i < j)
  let c1 := pairs.map (fun ⟨i,j⟩ =>
    let vi := (local.find? (·.chart = i)).getD {chart:=i, value:=0.0}
    let vj := (local.find? (·.chart = j)).getD {chart:=j, value:=0.0}
    let δ  := overlap * (vi.value - vj.value)
    (i,j,δ))
  { c0 := local, c1 := c1 }

/-- Čech obstruction: ℓ¹ norm of 1-cochain; nonzero ⇒ gluing inconsistency. -/
def obstructionL1 (C : CechComplex) : Float :=
  C.c1.foldl (fun acc (_,_,δ) => acc + Float.abs δ) 0.0

/-- Simple τ pulse aggregator (Chebyshev-like geometric decay surrogate). -/
def pulse (xs : List Float) : List TauPulse :=
  let α : Float := 0.33
  let rec go (k : Nat) (accE τ : Float) (rest : List Float) (out : List TauPulse) :=
    match rest with
    | []      => out.reverse
    | x :: rs =>
      let e' : Float := accE * (1.0 - α) + Float.abs x
      let τ' : Float := τ + (Float.abs x) / (1.0 + e')
      go (k+1) e' τ' rs ({k:=k, tau:=τ', energy:=e'} :: out)
  go 0 0.0 0.0 xs []

/-- Deterministic FNV-1a 64-bit hash for attestation (hex string). -/
def fnv1a64 (s : String) : String :=
  let off : UInt64 := 0xcbf29ce484222325
  let prime : UInt64 := 0x00000100000001B3
  let h := s.foldl (init := off) (fun h c => (h ^^^ (UInt64.ofNat c.toNat)) * prime)
  let hex := (Nat.iterate 16 (fun (acc, v : String × UInt64) =>
                let nib := v.land 0xFUL |>.toNat
                let ch  := "0123456789abcdef".get! nib
                (String.push acc ch, v >>> 4)) ("", h)).fst
  "0x" ++ hex.reverse

/-- Manifest line for a τ pulse. -/
def pulseJson (p : TauPulse) : String :=
  s!"{{\"k\":{p.k},\"tau\":{p.tau},\"energy\":{p.energy}}}"

def pulsesJson (ps : List TauPulse) : String :=
  "[" ++ String.intercalate "," (ps.map pulseJson) ++ "]"

end TauCrystal.Sheaf
LEAN

# --- Econ + Risk: presheaf ROI on instruments, Welford variance, systemic risk cert
cat > TauCrystal/EconRisk.lean <<'LEAN'
import Std
import TauCrystal/Sheaf

namespace TauCrystal.EconRisk

open Std TauCrystal.Sheaf

structure Instrument where
  id   : Nat
  name : String
deriving Repr, Inhabited, BEq

structure Morphism where
  src  : Instrument
  dst  : Instrument
  tag  : String
deriving Repr, Inhabited

/-- Presheaf ROI: assign a local section (expected return) to each instrument in an open set. -/
def roiPresheaf (U : List Instrument) (roi : Instrument -> Float) : List Section :=
  U.map (fun i => { chart := i.id, value := roi i })

/-- Pulse ROI over time to a τ-series that will be glued by the sheaf layer. -/
def roiTau (samples : List Float) : List TauPulse :=
  pulse samples

/-- Welford running variance for systemic risk. -/
structure Welford where
  n  : Nat := 0
  μ  : Float := 0.0
  M2 : Float := 0.0
deriving Repr

def Welford.step (w : Welford) (x : Float) : Welford :=
  let n' := w.n + 1
  let δ  := x - w.μ
  let μ' := w.μ + δ / Float.ofNat n'
  let M2':= w.M2 + δ * (x - μ')
  { n := n', μ := μ', M2 := M2' }

def Welford.var (w : Welford) : Float :=
  if w.n < 2 then 0.0 else w.M2 / Float.ofNat (w.n - 1)

/-- Systemic risk certificate derived from ROI τ-series dispersion. -/
structure RiskCert where
  mean    : Float
  variance: Float
  level   : String
deriving Repr, Inhabited

def certifyRisk (xs : List Float) : RiskCert :=
  let w := xs.foldl (fun acc x => acc.step x) {}
  let σ2 := w.var
  let μ  := w.μ
  let lvl :=
    if σ2 < 1e-4 then "neutral"
    else if σ2 < 1e-2 then "elevated"
    else if σ2 < 1e-1 then "high"
    else "critical"
  { mean := μ, variance := σ2, level := lvl }

/-- JSON encoders (manual). -/
def riskJson (r : RiskCert) : String :=
  s!"{{\"mean\":{r.mean},\"variance\":{r.variance},\"level\":\"{r.level}\"}}"

end TauCrystal.EconRisk
LEAN

# --- Topology: persistence-like bars from thresholded series; bottleneck vs reference
cat > TauCrystal/Topology.lean <<'LEAN'
import Std

namespace TauCrystal.Topology

open Std

structure Bar where
  birth : Nat
  death : Nat
  height : Float
deriving Repr, Inhabited

/-- Extract bars by thresholded plateau detection; deterministic scanning. -/
def bars (xs : List Float) (θ : Float := 0.0) : List Bar :=
  let rec go (i : Nat) (open? : Bool) (b : Nat) (hmax : Float) (rest : List Float) (out : List Bar) :=
    match rest with
    | [] =>
      if open? then {birth := b, death := i, height := hmax} :: out |>.reverse else out.reverse
    | x :: rs =>
      let above := x > θ
      match open?, above with
      | false, false => go (i+1) false b hmax rs out
      | false, true  => go (i+1) true i x rs out
      | true,  true  => go (i+1) true b (Float.max hmax x) rs out
      | true,  false => go (i+1) false b hmax rs ({birth := b, death := i, height := hmax} :: out)
  go 0 false 0 0.0 xs []

/-- Total lifetime and total mass for a barcode. -/
def lifetime (bs : List Bar) : Nat :=
  bs.foldl (fun acc b => acc + (b.death - b.birth)) 0

def mass (bs : List Bar) : Float :=
  bs.foldl (fun acc b => acc + (Float.ofNat (b.death - b.birth)) * b.height) 0.0

/-- Simple bottleneck distance against a reference barcode: max |Δlength| over greedy match. -/
def bottleneck (a b : List Bar) : Float :=
  let lenA := a.length
  let lenB := b.length
  let n := Nat.min lenA lenB
  let pairs := (List.range n).map (fun i => (a.get! i, b.get! i))
  pairs.foldl (fun acc ⟨x,y⟩ =>
    let la := Float.ofNat (x.death - x.birth)
    let lb := Float.ofNat (y.death - y.birth)
    Float.max acc (Float.abs (la - lb))) 0.0

def barJson (b : Bar) : String :=
  s!"{{\"birth\":{b.birth},\"death\":{b.death},\"height\":{b.height}}}"

def barsJson (bs : List Bar) : String :=
  "[" ++ String.intercalate "," (bs.map barJson) ++ "]"

end TauCrystal.Topology
LEAN

# --- Robust: runtime stabilizer with z-score clamp and tail audit
cat > TauCrystal/Robust.lean <<'LEAN'
import Std

namespace TauCrystal.Robust

open Std

/-- Z-score normalizer with clamp and tail count for audit. -/
structure RobustSig where
  mean    : Float
  std     : Float
  tails   : Nat
  clipped : Nat
deriving Repr, Inhabited

def meanStd (xs : List Float) : Float × Float :=
  let n : Float := Float.ofNat xs.length
  if xs.isEmpty then (0.0, 0.0)
  else
    let μ := xs.foldl (· + ·) 0.0 / n
    let σ := Float.sqrt ((xs.foldl (fun a x => a + (x - μ)*(x - μ)) 0.0) / n)
    (μ, σ)

/-- Stabilize a series: center, scale, clamp to ±k, report tail/clipping stats. -/
def stabilize (xs : List Float) (k : Float := 3.0) : (List Float) × RobustSig :=
  if xs.isEmpty then ([], {mean:=0.0,std:=0.0,tails:=0,clipped:=0})
  else
    let (μ, σ) := meanStd xs
    let denom := if σ == 0.0 then 1.0 else σ
    let rec f (rest : List Float) (out : List Float) (tails clipped : Nat) :=
      match rest with
      | [] => (out.reverse, {mean:=μ,std:=σ,tails:=tails,clipped:=clipped})
      | x::rs =>
        let z := (x - μ) / denom
        let tails' := if Float.abs z > k then tails + 1 else tails
        let zc := Float.max (Float.neg k) (Float.min k z)
        let clipped' := if zc != z then clipped + 1 else clipped
        f rs (zc :: out) tails' clipped'
    f xs [] 0 0

def robustJson (r : RobustSig) : String :=
  s!"{{\"mean\":{r.mean},\"std\":{r.std},\"tails\":{r.tails},\"clipped\":{r.clipped}}}"

end TauCrystal.Robust
LEAN

# --- Stratify: shard colimit and near-linear scaling estimator
cat > TauCrystal/Stratify.lean <<'LEAN'
import Std

namespace TauCrystal.Stratify

open Std

structure Stratum where
  id   : Nat
  size : Nat
deriving Repr, Inhabited

def colimitSize (ss : List Stratum) : Nat :=
  ss.foldl (fun acc s => acc + s.size) 0

/-- Empirical near-linear cost model: a*Σn_k + b*len(ss). -/
structure CostModel where
  a : Float
  b : Float
  cost : Float
deriving Repr, Inhabited

def estimateCost (ss : List Stratum) (a b : Float := (1.0, 0.05)) : CostModel :=
  let n := Float.ofNat (colimitSize ss)
  let m := Float.ofNat ss.length
  let c := a * n + b * m
  { a := a, b := b, cost := c }

def strataJson (ss : List Stratum) : String :=
  let one (s : Stratum) := s!"{{\"id\":{s.id},\"size\":{s.size}}}"
  "[" ++ String.intercalate "," (ss.map one) ++ "]"

end TauCrystal.Stratify
LEAN

# --- Fusion main: builds a coherent manifest tying all kernels, writes JSON
cat > FusionMain.lean <<'LEAN'
import Std
import TauCrystal/Sheaf
import TauCrystal/EconRisk
import TauCrystal/Topology
import TauCrystal/Robust
import TauCrystal/Stratify

open Std
open TauCrystal

structure Manifest where
  hashKey    : String
  pulses     : String
  risk       : String
  bars       : String
  robust     : String
  strata     : String
  lifetime   : Nat
  mass       : Float
  bottleneck : Float
  cost       : Float
deriving Repr

def manifestJson (m : Manifest) : String :=
  s!"{{\"hash\":\"{m.hashKey}\",\"pulses\":{m.pulses},\"risk\":{m.risk},\"bars\":{m.bars},\"robust\":{m.robust},\"strata\":{m.strata},\"lifetime\":{m.lifetime},\"mass\":{m.mass},\"bottleneck\":{m.bottleneck},\"cost\":{m.cost}}}"

def demoROI : List Float :=
  -- synthetic but deterministic ROI stream with regime change
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
    [{id:=0, size:=50000}, {id:=1, size:=50000}, {id:=2, size:=40000}]
  let cm := Stratify.estimateCost shards 1.0 0.05
  let key := Sheaf.fnv1a64 (toString ps ++ toString risk ++ toString bars ++ toString sig)
  let mani : Manifest := {
    hashKey    := key
    pulses     := Sheaf.pulsesJson ps
    risk       := EconRisk.riskJson risk
    bars       := Topology.barsJson bars
    robust     := Robust.robustJson sig
    strata     := Stratify.strataJson shards
    lifetime   := life
    mass       := mass
    bottleneck := bn
    cost       := cm.cost
  }
  let js := manifestJson mani
  IO.FS.createDirAll "manifests"
  IO.FS.writeFile "manifests/tau_fusion.json" js
  IO.println s!"wrote manifests/tau_fusion.json (hash={key})"
LEAN

# --- Wire lightweight imports into Main.lean without breaking existing content
ensure_line () {
  local file="$1" line="$2"
  grep -Fqx "$line" "$file" || echo "$line" >> "$file"
}
ensure_line Main.lean 'import TauCrystal/Sheaf'
ensure_line Main.lean 'import TauCrystal/EconRisk'
ensure_line Main.lean 'import TauCrystal/Topology'
ensure_line Main.lean 'import TauCrystal/Robust'
ensure_line Main.lean 'import TauCrystal/Stratify'
if ! grep -q 'def fusionReady' Main.lean; then
  cat >> Main.lean <<'LEAN'

def fusionReady : Bool := true
LEAN
fi

# ===================== BUILD + RUN + HASH + COMMIT =====================
echo "[lake] update …"
lake update || true
echo "[lake] build …"
lake build

echo "[lean --run] FusionMain (emit manifest) …"
lake env lean --run FusionMain.lean

echo "[sha256sum] manifests/tau_fusion.json"
if command -v sha256sum >/dev/null 2>&1; then
  sha256sum manifests/tau_fusion.json | awk '{print $1}' > manifests/tau_fusion.sha256
elif command -v shasum >/dev/null 2>&1; then
  shasum -a 256 manifests/tau_fusion.json | awk '{print $1}' > manifests/tau_fusion.sha256
else
  echo "sha256 tool not found; skipping external hash (internal FNV hash present)."
fi

git add TauCrystal/*.lean FusionMain.lean Main.lean manifests/tau_fusion.json manifests/tau_fusion.sha256 || true
if git diff --cached --quiet; then
  echo "No changes to commit."
else
  git commit -m "τ‑Crystal: full fusion integration (Sheaf/Cech, Econ+Risk, Topology bars, Robust z‑clamp, Stratify cost) + manifest emitter"
fi

git push -u origin "$BRANCH"
echo "Fusion complete. Branch: $BRANCH"
