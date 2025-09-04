import Batteries

namespace TauCrystal

structure Args where
  tau   : String := "1.0"
  q     : List String := []
  runId : String := ""
  out   : String := "manifest.json"
  audit : Bool := false
deriving Repr

def parseCSV (s : String) : List String :=
  s.split (· = ',') |>.map (·.trim) |>.filter (· ≠ "")

-- simple decimal parser: [+/-]digits[.digits], no exponents
def pow10 : Nat → Nat
| 0     => 1
| n+1   => pow10 n * 10

def parseDecFloat (s : String) : Option Float :=
  let t := s.trim
  let (neg, u) :=
    if t.startsWith "-" then (true, t.drop 1)
    else if t.startsWith "+" then (false, t.drop 1)
    else (false, t)
  let parts := u.split (· = '.')
  let sgn : Float := if neg then (-1.0) else 1.0
  match parts with
  | [a] =>
      match a.toNat? with
      | some ai =>
          let f := Float.ofInt (Int.ofNat ai)
          some (sgn * f)
      | none => none
  | [a,b] =>
      match a.toNat?, b.toNat? with
      | some ai, some bi =>
          let num := ai * pow10 b.length + bi
          let denom := pow10 b.length
          let fnum  := Float.ofInt (Int.ofNat num)
          let fden  := Float.ofInt (Int.ofNat denom)
          some (sgn * (fnum / fden))
      | _, _ => none
  | _ => none

def parseAllFloats (xs : List String) : Option (List Float) :=
  xs.foldr (fun s acc =>
    match parseDecFloat s, acc with
    | some f, some ys => some (f :: ys)
    | _, _            => none) (some [])

def jsonEscape (s : String) : String :=
  let rec loop (cs : List Char) (acc : String) :=
    match cs with
    | [] => acc
    | c :: cs =>
      let piece :=
        match c with
        | '\"' => "\\\""
        | '\\' => "\\\\"
        | '\n' => "\\n"
        | '\r' => "\\r"
        | '\t' => "\\t"
        | c    => String.singleton c
      loop cs (acc ++ piece)
  "\"" ++ loop s.data "" ++ "\""

def numArray (fs : List Float) : String :=
  "[" ++ String.intercalate "," (fs.map toString) ++ "]"

def writeManifest
  (runId : String) (audit : Bool) (tau : Float) (qs : List Float)
  (scaled : List Float) (qsum : Float) (_qmean : Float)
  (out : String) : IO Unit := do
  let qStr       := numArray qs
  let scaledStr  := numArray scaled
  let cnt        := qs.length
  let cntF       := Float.ofInt (Int.ofNat cnt)
  let content :=
    "{" ++
    s!"\"tau\": {toString tau}, " ++
    s!"\"q\": {qStr}, " ++
    s!"\"run_id\": {jsonEscape runId}, " ++
    s!"\"audit\": {(if audit then "true" else "false")}, " ++
    s!"\"count\": {cnt}, " ++
    s!"\"sum_q\": {toString qsum}, " ++
    s!"\"mean_q\": {toString (if cnt = 0 then 0.0 else qsum / cntF)}, " ++
    s!"\"scaled\": {scaledStr}" ++
    "}"
  IO.FS.writeFile out content
  IO.println s!"wrote {out}"

partial def parseArgs : List String → Args → Except String Args
| [], a => .ok a
| "--" :: xs, a            => parseArgs xs a
| "--tau" :: x :: xs, a    => parseArgs xs { a with tau := x }
| "--q"   :: x :: xs, a    => parseArgs xs { a with q := parseCSV x }
| "--run-id" :: x :: xs, a => parseArgs xs { a with runId := x }
| "--out" :: x :: xs, a    => parseArgs xs { a with out := x }
| "--audit" :: x :: xs, a  =>
    let v := x.toLower
    if v = "true" then parseArgs xs { a with audit := true }
    else if v = "false" then parseArgs xs { a with audit := false }
    else .error s!"bad --audit {x}"
| y :: _, _ => .error s!"unknown arg {y}"

def run (argv : List String) : IO UInt32 := do
  match parseArgs argv {} with
  | .error e => do
      IO.eprintln s!"error: {e}"
      IO.eprintln "usage: --tau <float> --q \"0,0.5,1\" --run-id <id> --out <file> --audit <true|false>"
      pure 2
  | .ok a =>
      match parseDecFloat a.tau, parseAllFloats a.q with
      | some tauF, some qF =>
          let scaled := qF.map (· * tauF)
          let qsum   := qF.foldl (· + ·) 0.0
          let cnt    := qF.length
          let cntF   := Float.ofInt (Int.ofNat cnt)
          let mean   := if cnt = 0 then 0.0 else qsum / cntF
          writeManifest a.runId a.audit tauF qF scaled qsum mean a.out
          pure 0
      | _, _ => do
          IO.eprintln "error: could not parse tau or q as decimals (only forms like 1.25, 0.5 are supported)"
          pure 2

end TauCrystal
