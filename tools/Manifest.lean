import Std
import Tools.GPU

namespace Tools
namespace Manifest

open Tools

structure Manifest where
  runId       : String
  diagnostics : List String
  auditorOk   : Bool
deriving Repr

def attachCech (m : Manifest) (c : GPU.Certificate) : Manifest :=
  { m with
    diagnostics :=
      m.diagnostics ++
      [s!"cech_obstruction: digest={c.matrixDigest}, primes={c.primes}, r0={c.r0}, r1={c.r1}, obs={c.obstructionDim}"] }

/-â€“ minimal JSON helpers (no external deps) -/
private def jsonEscape (s : String) : String :=
  -- escape backslash and quote; add more as needed
  let s := s.replace "\\" "\\\\"
  let s := s.replace "\"" "\\\""
  s

private def jstr (s : String) : String :=
  s!"\"{jsonEscape s}\""

private def jarr (xs : List String) : String :=
  "[" ++ String.intercalate ", " xs ++ "]"

def toJson (m : Manifest) (c : GPU.Certificate) (tau : Float) (qs : List Float) : String :=
  let diags   := jarr (m.diagnostics.map jstr)
  let primes  := jarr (c.primes.map (fun n => toString n))
  let qvals   := jarr (qs.map (fun x => s!"{x}"))
  "{" ++
    "\"runId\": "        ++ jstr m.runId ++ ", " ++
    "\"auditorOk\": "    ++ (if m.auditorOk then "true" else "false") ++ ", " ++
    "\"tau\": "          ++ s!"{tau}" ++ ", " ++
    "\"qVals\": "        ++ qvals ++ ", " ++
    "\"certificate\": {" ++
      "\"matrixDigest\": "   ++ jstr c.matrixDigest ++ ", " ++
      "\"primes\": "         ++ primes ++ ", " ++
      "\"r0\": "             ++ toString c.r0 ++ ", " ++
      "\"r1\": "             ++ toString c.r1 ++ ", " ++
      "\"obstructionDim\": " ++ s!"{c.obstructionDim}" ++
    "}, " ++
    "\"diagnostics\": "   ++ diags ++
  "}"
  
end Manifest
end Tools
