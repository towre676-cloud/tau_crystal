import Lake
open Lake DSL

package tau_crystal where

  "https://github.com/leanprover-community/batteries" @ "v4.22.0"

lean_lib tau_crystal_lib where
  roots := #[`TauCrystal]

@[default_target]
lean_exe tau_crystal where
  root := `Main2
