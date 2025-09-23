#!/usr/bin/env bash
set -euo pipefail; set +H

in_tsv="${1:-docs/prim/examples_abelian.tsv}"
out_dir=".tau_ledger/prim"
mkdir -p "$out_dir"
ts="$(date -u +%Y%m%dT%H%M%SZ)"
rid="primA-${ts}-${RANDOM}"
rec="$out_dir/receipt-$rid.tsv"
sha=$(sha256sum "$in_tsv" | awk "{print \$1}")

powmod() {
  base="$1"; exp="$2"; mod="$3";
  b=$(( (base%%mod+mod)%%mod )); e="$exp"; m="$mod"; r=1
  while [ "$e" -gt 0 ]; do
    if [ $((e & 1)) -eq 1 ]; then r=$(( (r*b)%%m )); fi
    b=$(( (b*b)%%m )); e=$((e>>1))
  done
  printf "%s" "$r"
}

gcd() { a=$1; b=$2; a=${a#-}; b=${b#-}; while [ "$b" -ne 0 ]; do t=$((a%%b)); a=$b; b=$t; done; printf "%s" "$a"; }
absf() { awk -v x="$1" '{print (x<0)?-x:x}'; }
logf() { awk -v x="$1" 'BEGIN{if (x<=0){print "nan"} else {print log(x)}}'; }

: > "$rec"
printf "%s\t%s\n" "RUN_ID" "$rid" >> "$rec"
printf "%s\t%s\n" "INPUT" "$in_tsv" >> "$rec"
printf "%s\t%s\n" "INPUT_SHA256" "$sha" >> "$rec"
printf "%s\t%s\n" "UTC" "$(date -u +%Y-%m-%dT%H:%M:%SZ)" >> "$rec"

row=0
while IFS=$'\t' read -r N G H K FACT COMM; do
  row=$((row+1))
  if [ "$row" -eq 1 ]; then continue; fi
  if [ -z "${N:-}" ] || [ -z "${G:-}" ] || [ -z "${H:-}" ] || [ -z "${K:-}" ] || [ -z "${FACT:-}" ]; then
    printf "%s\t%s\t%s\n" "ROW" "$row" "ERROR:missing field" >> "$rec"; continue
  fi
  if [ "$N" -le 1 ]; then printf "%s\t%s\t%s\n" "ROW" "$row" "ERROR:bad modulus" >> "$rec"; continue; fi
  gdn=$(gcd "$G" "$N")
  local_ok="NO"; if [ "$gdn" -eq 1 ]; then
    lhs=$(powmod "$G" "$K" "$N")
    if [ "$lhs" -eq $(( (H%N+N)%N )) ]; then local_ok="YES"; fi
  fi
  # Archimedean balance: |log|H|| ≈ K * log|G||
  lg=$(logf "${G#-}"); lh=$(logf "${H#-}")
  eps="1e-9"; ark="NO"
  if [ "$lg" != "nan" ] && [ "$lh" != "nan" ]; then
    diff=$(awk -v lh="$lh" -v lg="$lg" -v k="$K" 'BEGIN{print (lh - k*lg)}')
    ad=$(absf "$diff")
    ok=$(awk -v d="$ad" -v e="$eps" 'BEGIN{print (d<=e)?"YES":"NO"}')
    ark="$ok"
  fi
  global="NO"; if [ "$local_ok" = "YES" ] && [ "$ark" = "YES" ]; then global="YES"; fi
  printf "%s\t%s\n" "ROW" "$row" >> "$rec"
  printf "%s\t%s\n" "N" "$N" >> "$rec"
  printf "%s\t%s\n" "G" "$G" >> "$rec"
  printf "%s\t%s\n" "H" "$H" >> "$rec"
  printf "%s\t%s\n" "K" "$K" >> "$rec"
  printf "%s\t%s\n" "FACTORS" "$FACT" >> "$rec"
  printf "%s\t%s\n" "LOCAL_OK" "$local_ok" >> "$rec"
  printf "%s\t%s\n" "ARK_BALANCED" "$ark" >> "$rec"
  printf "%s\t%s\n" "GLOBAL_OK" "$global" >> "$rec"
  printf "%s\t%s\n" "WITNESS_MOD_N" "${lhs:-NA}" >> "$rec"
  printf "%s\t%s\n" "COMMENT" "${COMM:-}" >> "$rec"
  printf "%s\n" "---" >> "$rec"
done < "$in_tsv"

printf "%s\t%s\n" "RECEIPT_SHA256" "$(sha256sum "$rec" | awk "{print \$1}")" >> "$rec"
printf "%s\n" "OK: wrote $rec"
