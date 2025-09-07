#!/usr/bin/env bash
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")"/.. && pwd)"
cd "$root"
mkdir -p TauCrystal
cat > lakefile.lean << "EOF"
import Lake
open Lake DSL

package tau_crystal

-- Build the TauCrystal library (only what’s under TauCrystal/)
lean_lib TauCrystal where
  globs := #[.submodules `TauCrystal]

-- Keep the tiny fusion tool
lean_exe fusion where
  root := `FusionMain
EOF
cat > FusionMain.lean << "EOF"
import TauCrystal.Init

def main : IO Unit := do
  IO.println s!"tau_crystal fusion stub (lib {TauCrystal.version})"
EOF
