#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
mode=${1:-}
[ "$mode" = "dirac" ] || [ "$mode" = "weinberg" ] || { echo "usage: $0 {dirac|weinberg}"; exit 2; }
printf "
" "$mode" > docs/sm_complete/NEUTRINO_TOGGLE.txt
sed -i.bak "s/\("neutrino_mode": \)".*"/"$mode"/" receipts/sm_complete/sm_complete.meta.json && rm -f receipts/sm_complete/sm_complete.meta.json.bak
./scripts/sm_hash.sh && ./scripts/sm_verify.sh
