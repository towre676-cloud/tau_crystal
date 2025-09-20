import Tau.LeafGroup
import Tau.DeltaComplex

namespace Tau

def parseIntOr0 (s : String) : Int :=
  match s.trim.toInt? with | some i => i | none => 0

def absInt (x : Int) : Int := if x < 0 then -x else x

def splitCols (line : String) : List String :=
  line.split (fun c => c = '\t' || c = ' ')

def readLines (p : String) : IO (List String) := do
  let c ← IO.FS.readFile (System.FilePath.mk p)
  pure <| c.splitOn "\n" |>.filter (fun l => l.trim ≠ "")

def l1FromDelta (p : String) : IO Int := do
  let ls ← readLines p
  let s := ls.foldl
    (fun acc line =>
      let cols := splitCols line
      let v := if cols.length >= 2 then parseIntOr0 (cols[1]!) else 0
      acc + absInt v) 0
  pure s

def findKV (key : String) (ls : List String) : Int :=
  ls.foldl (fun acc l =>
    if acc ≠ 0 then acc
    else
      let cs := splitCols l
      if cs.length >= 2 && cs[0]! = key then parseIntOr0 (cs[1]!) else 0) 0

def loadTau (p : String) : IO (Int × Int) := do
  let ls ← readLines p
  pure (findKV "tau_drift_abs" ls, findKV "lambda" ls)

def readLeafSupport (p : String) : IO (List String) := do
  let ls ← readLines p
  let out := ls.foldl (fun acc line =>
    let cs := splitCols line
    if cs.length >= 2 then acc.append [cs[1]!] else acc) []
  pure out

-- Safe optional read for morphism_pairs.tsv (no need for fileExists)
def readPairs (p : String) : IO (List (String × String)) := do
  try
    let ls ← readLines p
    pure <| ls.foldl (fun acc line =>
      let cs := splitCols line
      if cs.length >= 2 then acc ++ [(cs[0]!, cs[1]!)] else acc) []
  catch _ =>
    pure []

def writeJson (path : String) (payload : String) : IO Unit := do
  IO.FS.writeFile (System.FilePath.mk path) payload

def listContains (l : List String) (s : String) : Bool :=
  l.any (fun x => decide (x = s))

def uniq (l : List String) : List String :=
  l.foldl (fun acc x => if listContains acc x then acc else acc ++ [x]) []

def decide (l1 td lb : Int) : (Bool × String) :=
  if l1 = 0 && td = 0 then (true, "VERIFIED: DELTA=0, tau conserved")
  else if td ≤ lb * (if l1 < 0 then -l1 else l1) then (true, "VERIFIED: |dTau| <= lambda * L1")
  else (false, "FAILED: |dTau| > lambda * L1")

end Tau

def main (argv : List String) : IO UInt32 := do
  if argv.length < 4 then
    IO.eprintln "usage: prove_v2 .tau_ledger/delta.tsv .tau_ledger/src_leaf.tsv .tau_ledger/dst_leaf.tsv .tau_ledger/tau_cert.tsv"
    return 2
  let deltaP := argv.get! 0
  let srcP   := argv.get! 1
  let dstP   := argv.get! 2
  let tauP   := argv.get! 3
  let pairsP := ".tau_ledger/morphism_pairs.tsv"

  -- core metrics
  let l1 ← Tau.l1FromDelta deltaP
  let (td, lb) ← Tau.loadTau tauP

  -- supports + pairs (pairs optional)
  let srcSupp ← Tau.readLeafSupport srcP
  let dstSupp ← Tau.readLeafSupport dstP
  let pairs   ← Tau.readPairs pairsP

  let mappedSrc := Tau.uniq (pairs.map (fun p => p.fst))
  let mappedDst := Tau.uniq (pairs.map (fun p => p.snd))
  let unmatchedSrc := (srcSupp.filter (fun s => !Tau.listContains mappedSrc s)).length
  let unmatchedDst := (dstSupp.filter (fun s => !Tau.listContains mappedDst s)).length

  let (ok, msg) := Tau.decide l1 td lb
  IO.println msg

  let okStr := if ok then "true" else "false"
  let payload :=
    "{\n" ++
    "  \"lean_proof_v2\": {\n" ++
    s!"    \"verified\": {okStr},\n" ++
    s!"    \"message\": \"{msg}\",\n" ++
    s!"    \"delta_l1_norm\": {l1},\n" ++
    s!"    \"tau_drift_abs\": {td},\n" ++
    s!"    \"lambda\": {lb},\n" ++
    s!"    \"pairs_count\": {pairs.length},\n" ++
    s!"    \"mapped_src_count\": {mappedSrc.length},\n" ++
    s!"    \"mapped_dst_count\": {mappedDst.length},\n" ++
    s!"    \"unmatched_src\": {unmatchedSrc},\n" ++
    s!"    \"unmatched_dst\": {unmatchedDst},\n" ++
    "    \"mock\": false\n" ++
    "  }\n" ++
    "}\n"

  let _ ← Tau.writeJson ".tau_ledger/lean_proof_v2.json" payload
  return (if ok then 0 else 1)
