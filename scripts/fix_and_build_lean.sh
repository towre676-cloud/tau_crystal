#!/usr/bin/env bash
set -euo pipefail
set +H
ROOT="$HOME/Desktop/tau_crystal/tau_crystal"; cd "$ROOT" || { echo "[err] bad root: $ROOT"; exit 1; }
export PATH="$HOME/.elan/bin:$PATH"
bak="lakefile.lean.bak.$(date +%Y%m%dT%H%M%SZ)"; [ -f lakefile.lean ] && cp -f lakefile.lean "$bak" || true
: > lakefile.lean
printf "%s\n" "import Lake" >> lakefile.lean
printf "%s\n" "open Lake DSL" >> lakefile.lean
printf "\n" >> lakefile.lean
printf "%s\n" "package tau_crystal" >> lakefile.lean
printf "\n" >> lakefile.lean
printf "%s\n" "lean_lib TauCrystal" >> lakefile.lean
printf "\n" >> lakefile.lean
printf "%s\n" "@[default_target]" >> lakefile.lean
printf "%s\n" "lean_exe «tau_proofs» where" >> lakefile.lean
printf "%s\n" "  root := \`Main" >> lakefile.lean
[ -f Main.lean ] || { : > Main.lean; printf "%s\n" "def main : IO Unit :=" >> Main.lean; printf "%s\n" "  IO.println \"τ-Crystal Lean stub OK\"" >> Main.lean; }
echo "[fix] lakefile.lean + Main.lean ready";
scripts/diag_wrap.sh bash -lc "export PATH=\"\$HOME/.elan/bin:\$PATH\"; lake update && lake build"
