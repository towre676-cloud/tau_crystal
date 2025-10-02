#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022
. ".yakfurby/bin/helpers.sh"; load_cfg
LED="$LEDGER_DIR/chain.tsv"; [ -s "$LED" ] || { echo "EMPTY"; exit 0; }
sed -n "1,20p" "$LED"
