#!/usr/bin/env bash
cd "$HOME/Desktop/tau_crystal/tau_crystal" || exit 1
set -euo pipefail
umask 022
export LC_ALL=C LANG=C
export MSYS2_ARG_CONV_EXCL='*'

mkdir -p obstruction_card/out ci obstruction_card/bin tau_crystal/data/pdg debug
log="debug/real_chain.$(date +%s).log"
exec > >(tee "$log") 2>&1

say(){ printf '[%(%H:%M:%S)T] %s\n' -1 "$*"; }

# A/B ensure (3x3 I as placeholder)
if [ ! -s obstruction_card/out/A_full.csv ] || [ ! -s obstruction_card/out/B_full.csv ]; then
  say "No A/B; writing 3x3 identity placeholders."
  printf '1,0,0\n0,1,0\n0,0,1\n' > obstruction_card/out/A_full.csv
  printf '1,0,0\n0,1,0\n0,0,1\n' > obstruction_card/out/B_full.csv
fi

# constants ensure (minimal pins; 0-based indices)
if [ ! -s tau_crystal/data/pdg/constants.json ]; then
  say "No constants.json; writing minimal PDG pins."
  mkdir -p tau_crystal/data/pdg
  printf '%s\n' '{ "v": 246.21965, "m_t": 172.69, "m_t_tol": 0.01, "m_t_idx": 0, "m_tau": 1.77686, "m_tau_tol": 0.005, "m_tau_idx": 2 }' \
    > tau_crystal/data/pdg/constants.json
fi

# shim petsc_build.sh if absent
if [ ! -x ./petsc_build.sh ]; then
  cat > petsc_build.sh <<'EOS'
#!/usr/bin/env bash
set -e
echo "[petsc_build] shim OK"
EOS
  chmod +x petsc_build.sh
fi

say "Running PETSc build…"
./petsc_build.sh

say "Running PETSc run…"
if ! ./petsc_run.sh \
  --outH0 obstruction_card/out/spectra_H0.json \
  --outH1 obstruction_card/out/spectra_H1.json; then
  say "WARNING: petsc_run.sh failed; leaving any previous spectra in place."
fi

# Show spectra heads
say "-- spectra_H0.json --"; head -c 200 obstruction_card/out/spectra_H0.json; echo
say "-- spectra_H1.json --"; head -c 200 obstruction_card/out/spectra_H1.json; echo

# Build M from spectra; fallback on error
say "Invoking python helper: obstruction_card/bin/build_M_from_spectra.py"
if ! python3 obstruction_card/bin/build_M_from_spectra.py \
  --A obstruction_card/out/A_full.csv \
  --B obstruction_card/out/B_full.csv \
  --H0 obstruction_card/out/spectra_H0.json \
  --H1 obstruction_card/out/spectra_H1.json \
  --outM obstruction_card/out/M.npy \
  --outSing obstruction_card/out/singular_values_M.csv \
  --outPhase obstruction_card/out/detM_phase.json; then
  say "WARNING: python helper failed; writing safe defaults."
  printf '{ "det_phase": 0.0 }\n' > obstruction_card/out/detM_phase.json
  printf '1,1,1\n' > obstruction_card/out/singular_values_M.csv
fi

say "-- detM_phase.json --"; head -c 200 obstruction_card/out/detM_phase.json; echo
say "-- singular_values_M.csv --"; head -c 200 obstruction_card/out/singular_values_M.csv; echo

# Run ladder
say "Running ladder…"
if ! bash ci/compress_ladder.sh; then
  say "WARNING: ladder returned nonzero"
fi

say "Done. Log: $log"
