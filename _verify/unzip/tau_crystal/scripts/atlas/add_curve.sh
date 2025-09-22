#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
# usage: add_curve.sh N LABEL a1 a2 a3 a4 a6
F="scripts/atlas/curves_canonical.tsv"
[ $# -eq 7 ] || { echo "usage: $0 N LABEL a1 a2 a3 a4 a6" >&2; exit 2; }
printf "%s\t%s\t%s\t%s\t%s\t%s\t%s\n" "$1" "$2" "$3" "$4" "$5" "$6" "$7" >> "$F"
echo "[atlas] appended $2 (N=$1) to $F"
