import Lake
open Lake DSL

package tau_crystal

-- Build only the known-good modules.
lean_lib TauCrystal where
  globs := #[
    .precise `TauCrystal.Edition
    -- add more when they compile:
    -- .precise `TauCrystal.EconRisk
    -- .precise `TauCrystal.Spectral
  ]

@[default_target] lean_exe fusion where
  root := `FusionMain
