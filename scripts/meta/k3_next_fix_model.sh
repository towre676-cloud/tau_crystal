#!/usr/bin/env bash
. "$(dirname "$0")/../safe/_env.sh"
set -e
CD="$HOME/Desktop/tau_crystal/tau_crystal"; cd "$CD" || exit 1
REC="receipts/k3_next_receipt.json"
A4="$1"; A6="$2"; DSIGN="$3"
[ -n "$A4" ] && [ -n "$A6" ] && [ -n "$DSIGN" ] || { echo "usage: k3_next_fix_model.sh <a4> <a6> <discriminant_sign(+1|-1)>" >&2; exit 2; }
python scripts/safe/json_set.py "$REC" curve.a4 "$A4"
python scripts/safe/json_set.py "$REC" curve.a6 "$A6"
python scripts/safe/json_set.py "$REC" curve.discriminant_sign "$DSIGN"
printf "%s\n" "model set: a4=$A4 a6=$A6 disc_sign=$DSIGN"
