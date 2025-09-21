import Lake
open Lake DSL

package «spectral_kernel» where
  -- you can set package options here

-- If your Lean files import Mathlib, keep this line; if they don't, you can remove it.
require mathlib from git "https://github.com/leanprover-community/mathlib4"

-- Tell Lake that your library's sources are under "Src/"
lean_lib «Spectral» where
  srcDir := "Src"

-- Executables that print JSON to stdout
lean_exe «plumbing» where
  -- maps to file: Src/Spectral/plumbing.lean  (module: Spectral.plumbing)
  root := `Spectral.plumbing
  supportInterpreter := true

lean_exe «face_plumbing» where
  -- maps to file: Src/Spectral/face_plumbing.lean  (module: Spectral.face_plumbing)
  root := `Spectral.face_plumbing
  supportInterpreter := true
