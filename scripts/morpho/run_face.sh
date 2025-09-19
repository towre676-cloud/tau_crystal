#!/usr/bin/env bash
set +e +o pipefail; umask 022; trap - ERR
scripts/morpho/procrustes_evenodd.sh analysis/morpho/input/landmarks_clean.csv .tau_ledger/morpho/procrustes.local
scripts/morpho/spectral_receipt.sh v_frontal analysis/morpho/input/landmarks_clean.csv .tau_ledger/morpho/v_frontal.local
scripts/geom/l_series_compose.sh .tau_ledger/morpho/global.L .tau_ledger/morpho/v_frontal.local .tau_ledger/morpho/procrustes.local
scripts/morpho/cert_mint.sh .tau_ledger/morpho/global.L
scripts/morpho/judge_latest.sh
scripts/morpho/bridge_and_publish.sh
PACK=$(ls -1dt analysis/morpho/packs/run_* 2>/dev/null | head -n 1)
scripts/morpho/pack_verify.sh "$PACK"
H=$(awk -F= '/^H_BAR=/{print $2}' "$PACK/global.L" | head -n1)
COUNT=$(find "$PACK" -maxdepth 1 -type f | wc -l | awk '{print $1}')
ROOT=$(awk '$1=="ROOT"{print $2}' "$PACK/corridor.receipt.tsv" | head -n1)
echo "published: $PACK  (H_BAR=$H, files=$COUNT, root=$ROOT)"
