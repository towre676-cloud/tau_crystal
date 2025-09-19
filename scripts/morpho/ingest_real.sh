#!/usr/bin/env bash
set -Ee -o pipefail; set +H; umask 022
[ "" = "1" ] && set -x
mesh_src="${1:-}"; lm_csv="${2:-}"; mod="${3:-v_frontal}"
[ -n "$mesh_src" ] && [ -f "$mesh_src" ] || { echo "usage: ingest_real.sh MESH_OR_IMAGE LEFT_RIGHT.csv [MOD]"; exit 2; }
[ -n "$lm_csv" ]  && [ -f "$lm_csv"  ]   || { echo "missing landmarks csv"; exit 2; }
ts=$(date -u +%Y%m%dT%H%M%SZ)
in_dir="analysis/morpho/input"; mkdir -p "$in_dir"
mesh_dst="$in_dir/${mod}.${ts}.bin"; cp -f "$mesh_src" "$mesh_dst"
lm_dst="$in_dir/landmarks_${ts}.csv"; cp -f "$lm_csv" "$lm_dst"
printf "%s\n" "FILE=$mesh_dst  SHA256=$(sha256sum "$mesh_dst"|awk "{print \$1}")" >> analysis/morpho/manifest.tsv
printf "%s\n" "FILE=$lm_dst    SHA256=$(sha256sum "$lm_dst"|awk "{print \$1}")"   >> analysis/morpho/manifest.tsv
out1=".tau_ledger/morpho/${mod}.local"; out2=".tau_ledger/morpho/procrustes.local"
scripts/morpho/spectral_receipt.sh "$mod" "$mesh_dst" "$out1"
scripts/morpho/procrustes_evenodd.sh "$lm_dst" "$out2"
scripts/geom/l_series_compose.sh .tau_ledger/morpho/global.L "$out1" "$out2"
scripts/morpho/cert_mint.sh .tau_ledger/morpho/global.L
latest=$(ls -1t analysis/morpho/certificates/cert_*.json | head -n 1)
scripts/morpho/cert_judge.sh "$latest"
echo "ingest: OK — $(basename "$latest") for $mod"
