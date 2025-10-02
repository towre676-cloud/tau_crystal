-- module: Spectral.plumbing (path-derived)
def main : IO Unit := do
  let json :=
    "{" ++
    "\"nodes\":[{\"label\":\"A\",\"maslov\":1,\"tamagawa\":1}," ++
               "{\"label\":\"B\",\"maslov\":0,\"tamagawa\":0}]," ++
    "\"edges\":[{\"from\":\"A\",\"to\":\"B\",\"int\":1}]}"
  IO.println json
