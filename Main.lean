import Batteries

structure Args where
  tau   : String := "1.0"
  q     : List String := []
  runId : String := ""
  out   : String := "manifest.json"
  audit : Bool := false
deriving Repr

def parseCSV (s : String) : List String :=
  s.split (· = ',') |>.map (·.trim) |>.filter (· ≠ "")

partial def parseArgs : List String → Args → Except String Args
| [], a => .ok a
| "--" :: xs, a            => parseArgs xs a                    -- ignore Lake's separator
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

def writeManifest (a : Args) : IO Unit := do
  let qStr := "[" ++ String.intercalate "," a.q ++ "]"
  let content :=
    "{" ++
    s!"\"tau\": {a.tau}, " ++
    s!"\"q\": {qStr}, " ++
    s!"\"run_id\": {jsonEscape a.runId}, " ++
    s!"\"audit\": {(if a.audit then "true" else "false")}" ++
    "}"
  IO.FS.writeFile a.out content
  IO.println s!"wrote {a.out}"

-- Receives argv from Main2 and returns exit code (0 on success)
def appMain (argv : List String) : IO UInt32 := do
  match parseArgs argv {} with
  | .ok a    => writeManifest a; pure 0
  | .error e =>
      IO.eprintln s!"error: {e}"
      IO.eprintln "usage: --tau <float> --q \"0,0.5,1\" --run-id <id> --out <file> --audit <true|false>"
      pure 2
