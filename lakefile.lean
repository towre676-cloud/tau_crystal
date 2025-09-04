import Lake
open Lake DSL

package tau_crystal where

lean_lib TauCrystal where
  globs := #[.submodules `TauCrystal]

lean_exe fusion where
  root := `FusionMain
  supportInterpreter := true
