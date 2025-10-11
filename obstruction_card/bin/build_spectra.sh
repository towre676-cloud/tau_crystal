#!/usr/bin/env bash
set -euo pipefail; umask 022; export LC_ALL=C LANG=C
# TODO: replace this echo stub with your mpirun PETSc call
# Example:
# mpirun -n 4 ./petsc_eig -A obstruction_card/out/A_full.csv -B obstruction_card/out/B_full.csv \
#   --outH0 obstruction_card/out/spectra_H0.json --outH1 obstruction_card/out/spectra_H1.json
: > obstruction_card/out/spectra_H0.json
: > obstruction_card/out/spectra_H1.json
printf '{ "evals": [1e-2,2e-2,3e-2] }\n' > obstruction_card/out/spectra_H0.json
printf '{ "evals": [1.5e-2,2.5e-2,3.5e-2] }\n' > obstruction_card/out/spectra_H1.json
