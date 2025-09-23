#!/usr/bin/env bash
set -euo pipefail; set +H
TXID="${1:?usage: record_broadcast.sh <txid> <block>}"
BLK="${2:?usage: record_broadcast.sh <txid> <block>}"
F="analysis/validation/corridor.receipt.tsv"
touch "$F"
TMP="$(mktemp)"
awk -v tx="$TXID" -v bk="$BLK" 'BEGIN{t=0;b=0}{if(/^txid=/){print "txid="tx; t=1} else if(/^block=/){print "block="bk; b=1} else {print}} END{if(!t) print "txid="tx; if(!b) print "block="bk}' "$F" > "$TMP"
mv "$TMP" "$F"
