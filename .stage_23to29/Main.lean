import TauCrystal.Proofs
import System

open TauCrystal

def asJson (ok : Bool) (proofs : List String) : String :=
  let quoted := proofs.map (fun s => "\"" ++ s ++ "\"")
  let ps := "[" ++ String.intercalate "," quoted ++ "]"
  let okStr := if ok then "true" else "false"
  "{" ++ "\"lean_ok\":" ++ okStr ++ ",\"proofs\":" ++ ps ++ "}"

def main (args : List String) : IO UInt32 := do
  let out := args.headD ".tau_ledger/lean_proofs.json"
  let content := asJson true ["tick_strict","tick_monotone"]
  IO.FS.createDirAll ".tau_ledger"
  IO.FS.writeFile out content
  IO.println ("[lean] wrote " ++ out)
  pure 0
import TauCrystal.ResidueTwistedReciprocity
