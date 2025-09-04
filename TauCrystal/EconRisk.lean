import Std
import TauCrystal.Sheaf
namespace TauCrystal.EconRisk
open Std TauCrystal.Sheaf

structure Instrument where
  id   : Nat
  name : String
deriving Repr, Inhabited, BEq

def roiPresheaf (U : List Instrument) (roi : Instrument → Float) : List Section :=
  U.map (fun i => { chart := i.id, value := roi i })

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

structure RiskCert where
  mean     : Float
  variance : Float
  level    : String
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

def riskJson (r : RiskCert) : String :=
  s!"{{\"mean\":{r.mean},\"variance\":{r.variance},\"level\":\"{r.level}\"}}"

end TauCrystal.EconRisk
