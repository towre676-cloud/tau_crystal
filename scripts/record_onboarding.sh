#!/usr/bin/env bash
# Produce an asciinema cast of the 60-second onboarding
# Requires: asciinema, git, python3 (Lean optional), cosign (optional)
set -euo pipefail
cast_file="tau-crystal-onboarding.cast"
echo "[+] Recording to $cast_file (Ctrl-D to stop)"
asciinema rec --overwrite "$cast_file" -c 'bash -c "
set -e
echo \"=== tau-crystal 60-second onboarding ===\"
echo \"1) Clone repo\"
git clone https://github.com/towre676-cloud/tau_crystal.git demo && cd demo
echo \"2) Stamp docs (deterministic)\"
python scripts/tauc.py stamp
echo \"3) Verify locally\"
PROOF_OF_WORK_BITS=8 python scripts/tauc.py verify
echo \"4) View manifest\"
head -20 tau-crystal-manifest.json
echo \"Done — artifacts stamped and verified.\"
"'
echo "[+] Cast ready. Upload to asciinema.org and embed the link."
