#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
REPO="${1:-.tau_ledger/receipts}"; OUT=".tau_ledger/interf/interference.svg"; mkdir -p .tau_ledger/interf
command -v jq >/dev/null 2>&1 || { echo "[err] requires jq"; exit 2; }
fields="commit merkle_root wrapper_digest tau_tensor entropy_delta_bytes"
mapfile -t files < <(ls -1 "$REPO"/*.json 2>/dev/null | LC_ALL=C sort || true)
[ "${#files[@]}" -gt 0 ] || { echo "[err] no receipts in $REPO"; exit 2; }
n=${#files[@]}; max=1
printf "%s\n" "<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"$((n*20))\" height=\"$((n*20))\">" > "$OUT"
for ((i=0;i<n;i++)); do for ((j=0;j<n;j++)); do diff=0; for k in $fields; do a=$(jq -r --arg k "$k" ".[$k] // \"\"" "${files[i]}"); b=$(jq -r --arg k "$k" ".[$k] // \"\"" "${files[j]}"); [ "$a" != "$b" ] && diff=$((diff+1)); done; op=$(awk -v v="$diff" -v m="$max" "BEGIN{print (m>0)?v/m:0}"); printf "%s\n" "<rect x=\"$((i*20))\" y=\"$((j*20))\" width=\"20\" height=\"20\" fill=\"#ff0000\" fill-opacity=\"$op\"/>" >> "$OUT"; done; done
printf "%s\n" "</svg>" >> "$OUT"; echo "[OK] interference map: $OUT"
