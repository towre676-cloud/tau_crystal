import Lake
open Lake DSL

package tau_crystal

-- Minimal libraries (no globs needed)
lean_lib TauCrystal
lean_lib Receipt

-- Single executable; point it to a Main module file
lean_exe app where
  root := `Main

-- std pin (harmless here; remove if you want)
require std from git "https://github.com/leanprover/std4" @ "v4.5.0"
target proofs : Unit := do
  let _ ← Lean.build (importString := "TauCrystal.Proofs.TauMonotonic")
  pure ()

target laurent_proofs : Unit := do
  let _ ← Lean.build (importString := "TauCrystal.Proofs.LaurentCheck")
  pure ()
