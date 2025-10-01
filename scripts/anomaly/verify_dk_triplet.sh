#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
. "$(dirname "$0")/_hash.sh"
[ $# -eq 4 ] || { echo "use: verify_dk_triplet.sh <dK.json> <bulk_logdet.json> <eta_boundary.json> <logB_receipt.json>" 1>&2; exit 2; }
J="$1"; BULK="$2"; ETA="$3"; REL="$4"
[ -s "$J" ] || { echo "[err] missing/empty JSON: $J"; exit 3; }
for p in "$BULK" "$ETA" "$REL"; do [ -f "$p" ] || { echo "[err] missing file: $p"; exit 4; }; done
tmp=".dk.$$.json"; trap 'rm -f "$tmp"' EXIT
tr -d "\r" < "$J" > "$tmp" || cp -f "$J" "$tmp"
val(){ awk -F"\\\"" -v k="$1" '$2==k{print $4;exit}' "$tmp"; }
typ="$(val type)"; [ "$typ" = "differential_K_triplet" ] || { echo "[err] type=$typ"; exit 5; }
bh="$(val bulk_K_index_hash)"; eh="$(val boundary_eta_hash)"; rh="$(val relative_logB_hash)"
cbh="$(hash_file "$BULK")"; ceh="$(hash_file "$ETA")"; crh="$(hash_file "$REL")"
[ "$bh" = "$cbh" ] || { echo "[err] bulk mismatch: json=$bh calc=$cbh"; exit 6; }
[ "$eh" = "$ceh" ] || { echo "[err] eta  mismatch: json=$eh calc=$ceh"; exit 7; }
[ "$rh" = "$crh" ] || { echo "[err] rel  mismatch: json=$rh calc=$crh"; exit 8; }
echo "[ok] verified: $J"
