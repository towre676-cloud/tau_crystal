import Lake
open Lake DSL

package «tau_crystal» where

lean_lib «TauCrystal» where
  -- include only modules under TauCrystal/ (Accel/* has been moved to legacy/)
  globs := #[.submodules `TauCrystal]

lean_exe «fusion» where
  root := `FusionMain
  supportInterpreter := true
