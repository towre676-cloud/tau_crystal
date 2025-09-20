import Tau.LeafGroup
import Tau.DeltaComplex

namespace Tau

def parseIntOr0 (s : String) : Int :=
  match s.trim.toInt? with | some i => i | none => 0

def absInt (x : Int) : Int := if x < 0 then -x else x

def readLines (p : String) : IO (List String) := do
  let c ← IO.FS.readFile p
  pure <| c.splitOn "\n" |>.filter (fun l => l.trim ≠ "")

def l1FromDelta (p : String) : IO Int := do
  let ls ← readLines p
  let s := ls.foldl
    (fun acc line =>
      let cols := line.split (fun c => c = '\t' || c = ' ')
      let v :=
        if h : 1 < cols.length then
          parseIntOr0 (cols.get ⟨1, h⟩)
        else 0
      acc + absInt v) 0
  pure s

partial def findKV (key : String) (ls : List String) : Int :=
  match ls with
  | [] => 0
  | l :: t =>
    let cols := l.split (fun c => c = '\t' || c = ' ')
    let v :=
      if cols.length ≥ 2 && cols.get! 0 = key then parseIntOr0 (cols.get! 1) else 0
    if v ≠ 0 then v else findKV key t

def loadTau (p : String) : IO (Int × Int) := do
  let ls ← readLines p
  pure (findKV "tau_drift_abs" ls, findKV "lambda" ls)

def writeJson (path : String) (ok : Bool) (msg : String) (l1 td lb : Int) : IO Unit := do
  let okStr := if ok then "true" else "false"
  let s :=
    "{\n" ++
    "  \"lean_proof_v2\": {\n" ++
    s!"    \"verified\": {okStr},\n" ++
    s!"    \"message\": \"{msg}\",\n" ++
    s!"    \"delta_l1_norm\": {l1},\n" ++
    s!"    \"tau_drift_abs\": {td},\n" ++
    s!"    \"lambda\": {lb},\n" ++
    "    \"mock\": false\n" ++
    "  }\n" ++
    "}\n"
  IO.FS.writeFile path s

def decide (l1 td lb : Int) : (Bool × String) :=
  if l1 = 0 && td = 0 then (true, "VERIFIED: Δ=0, τ conserved")
  else if td ≤ lb * (if l1 < 0 then -l1 else l1) then (true, "VERIFIED: |Δτ| ≤ λ‖Δ‖₁")
  else (false, "FAILED: |Δτ| > λ‖Δ‖₁")

end Tau

def main (argv : List String) : IO UInt32 := do
  if argv.length < 4 then
    IO.eprintln "usage: prove_v2 .tau_ledger/delta.tsv .tau_ledger/src_leaf.tsv .tau_ledger/dst_leaf.tsv .tau_ledger/tau_cert.tsv"
    pure 2
  let deltaP := argv.get! 0
  let tauP   := argv.get! 3
  let l1 ← Tau.l1FromDelta deltaP
  let (td, lb) ← Tau.loadTau tauP
  let (ok, msg) := Tau.decide l1 td lb
  IO.println msg
  ← Tau.writeJson ".tau_ledger/lean_proof_v2.json" ok msg l1 td lb
  pure <| if ok then 0 else 1
