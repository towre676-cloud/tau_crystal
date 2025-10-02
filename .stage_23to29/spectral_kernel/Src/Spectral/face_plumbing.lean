-- module: Spectral.face_plumbing
def main : IO Unit := do
  let json :=
    "{" ++
    "\"nodes\":[{\"label\":\"Patient-\\u03b1\",\"maslov\":1,\"tamagawa\":1}]," ++
    "\"edges\":[]}"
  IO.println json
