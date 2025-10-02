#!/usr/bin/env bash
cd "$HOME/Desktop/tau_crystal/tau_crystal" || exit 1
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
f="doc/monographs/volume2_descent_spectrum.md"; d=$(dirname "$f"); mkdir -p "$d"; : > "$f"
printf "%s\n" "# Volume II: Descent, Spectrum, and Obstruction" >> "$f"
printf "%s\n" "" >> "$f"
printf "%s\n" "This volume lifts 🪞τ‑Reflection from a runtime oracle to a corridor‑wide epistemic protocol."
printf "%s\n" "" >> "$f"
printf "%s\n" "• τSheaf(J,C) := Sheaf(J,C) × TauCapsule  (tailL1, ρ, ε)." >> "$f"
printf "%s\n" "• Descent chains are extracted from per‑module capsules (imports → chains)." >> "$f"
printf "%s\n" "• CorridorReceipt binds Lean capsules with τ‑Reflection capsules for attested reproducibility." >> "$f"
