# tau_crystal

Deterministic diagnostic runner with `cert` / `τ-pulse` / `qCRO`, a signed manifest, and linear-time work probes.

[![assure](https://github.com/towre676-cloud/tau_crystal/actions/workflows/assure.yml/badge.svg)](…link to workflow…)

## Quickstart (Bash)
$HOME/.elan/bin/lake.exe build
$HOME/.elan/bin/lake.exe exe tau_crystal -- --tau 1.25 --q "0,0.5,1,2" --run-id demo --out manifest.json --audit true

## Assurance
./assure.sh

## Probes
./tools/verify_linear.sh
./tools/verify_linear_reps.sh
