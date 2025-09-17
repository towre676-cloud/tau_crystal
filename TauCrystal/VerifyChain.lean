import Std
open Std
def lastTwoLines (s : String) : Option (String × String) :=
  let ls := s.splitOn "\n" |>.filter (·.trim ≠ "")
  match ls with
  | [] | [_] => none
  | _ => some (ls.get! (ls.length-2), ls.get! (ls.length-1))
def after (s pre : String) : Option String :=
  match s.indexOf? pre with
  | none => none
  | some i => some <| s.extract (i+pre.length) s.length
def untilQuote (s : String) : String :=
  match s.splitOn "\"" with
  | _ :: a :: _ => a
  | _ => ""
def parsePrev (json : String) : String :=
  match after json "\"prev\":\"" with
  | some t => untilQuote t
  | none => ""
def parsePath (line : String) : String :=
  match line.splitOn "\t" with
  | _ :: p :: _ => p
  | _ => ""
def parseHash (line : String) : String :=
  match line.splitOn "\t" with
  | h :: _ => h
  | _ => ""
def main : IO UInt32 := do
  let chain ← IO.FS.readFile ".tau_ledger/CHAIN"
  match lastTwoLines chain with
  | none => IO.println "[lean] CHAIN too short"; return 1
  | some (prevLine, lastLine) => do
      let prevHash := parseHash prevLine
      let recPath  := parsePath lastLine
      let js ← IO.FS.readFile recPath
      let prevField := parsePrev js
      if prevField == "" then IO.println "[lean] prev missing" *> pure 1
      else if prevField == prevHash then IO.println "[lean] chain OK" *> pure 0
      else IO.println s!"[lean] prev mismatch: {prevField} ≠ {prevHash}" *> pure 2
