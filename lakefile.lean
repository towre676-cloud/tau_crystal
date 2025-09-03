import Lake
open Lake DSL

package tau_crystal where

require batteries from git
  "https://github.com/leanprover-community/batteries" @ "v4.22.0"

-- Put project modules into a library so they are importable.
lean_lib tau_crystal_lib where
  roots := #[`Main]  -- add more roots here if you want to import them elsewhere

@[default_target]
lean_exe tau_crystal where
  root := `Main2
