import Std
open System

def main : IO Unit := do
  let dir  := FilePath.mk "manifests"
  let file := dir / "tau_fusion.json"
  IO.FS.createDirAll dir
  let json := "{\"schema\":\"tau-fusion@1\",\"ok\":true}\n"
  IO.FS.writeFile file json
  IO.println s!"wrote {file}"
