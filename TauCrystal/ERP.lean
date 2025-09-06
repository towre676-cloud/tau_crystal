import Lean
open Lean

namespace TauCrystal

def slurp (p : System.FilePath) : IO String := do
  let h ← IO.FS.readFile p
  pure h

def latestManifestPath : IO System.FilePath := do
  let entries ← System.FilePath.readDir "manifests"
  if entries.isEmpty then
    throw <| IO.userError "no manifests found"
  let files := entries.map (·.path) |>.qsort (·.toString < ·.toString)
  pure files.getLast!

def loadLatestManifest : IO String := do
  let p ← latestManifestPath
  slurp p

end TauCrystal
