import Lake
open Lake DSL

package tau_crystal

-- Build the TauCrystal library (only what’s under TauCrystal/)
lean_lib TauCrystal where
  globs := #[.submodules `TauCrystal]

-- Keep the tiny fusion tool
lean_exe fusion where
  root := `FusionMain
