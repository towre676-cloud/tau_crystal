#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022
: "${1:?usage: sense_env.sh <segment-id>}"
SEG_ID="$1"
OUTDIR=".yakfurby/run/$SEG_ID"; mkdir -p "$OUTDIR"
VSTAT="$OUTDIR/volt_status.txt"; TAMP="$OUTDIR/tamper_flag.txt"
have(){ command -v "$1" >/dev/null 2>&1; }
if have i2cget; then
  VRAW=$(i2cget -y 1 0x40 0x02 w 2>/dev/null || echo "0xFFFF")
  echo "$VRAW" > "$VSTAT"
else
  echo "no_i2c" > "$VSTAT"
fi
GPIOVAL="/sys/class/gpio/gpio17/value"
if [ -r "$GPIOVAL" ]; then
  TAMPFLAG=$(cat "$GPIOVAL" 2>/dev/null || echo "err")
  echo "$TAMPFLAG" > "$TAMP"
else
  echo "no_gpio" > "$TAMP"
fi
