#!/usr/bin/env bash
set -Ee -o pipefail; set +H; umask 022
mkdir -p analysis/morpho/input
printf "%s" "frontal-mesh-demo-bytes-v1" > analysis/morpho/input/frontal.mesh
printf "%s\n%s\n" "10,20,  -10,20" "12,18,  -12,18" > analysis/morpho/input/landmarks_lr.csv
scripts/morpho/spectral_receipt.sh v_frontal analysis/morpho/input/frontal.mesh .tau_ledger/morpho/v_frontal.local
scripts/morpho/procrustes_evenodd.sh analysis/morpho/input/landmarks_lr.csv .tau_ledger/morpho/procrustes.local
scripts/geom/l_series_compose.sh .tau_ledger/morpho/global.L .tau_ledger/morpho/v_frontal.local .tau_ledger/morpho/procrustes.local
scripts/morpho/cert_mint.sh .tau_ledger/morpho/global.L
latest=$(ls -1t analysis/morpho/certificates/cert_*.json | head -n 1)
scripts/morpho/cert_judge.sh "$latest"
echo "demo: OK — $(basename "$latest")"
