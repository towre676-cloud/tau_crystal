#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022

need(){ command -v "$1" >/dev/null 2>&1 || { echo "[adv] missing $1" >&2; exit 2; }; }
need jq
mkdir -p analysis/metrics

pick_index(){ # deterministic from CHAIN head
  local n="$1" head h8
  head=$(tail -n1 .tau_ledger/CHAIN | awk '{print $1}')
  h8=${head:0:8}
  printf '%d\n' $(( (16#$h8 % (n>0?n:1)) + 1 ))
}

bruteforce_count(){ # a1 a2 a3 a4 a6 p -> #E(F_p)
  awk -v a1="$1" -v a2="$2" -v a3="$3" -v a4="$4" -v a6="$5" -v p="$6" '
    function mod(x){ x%=p; if(x<0)x+=p; return x }
    function eqn(x,y,  LHS,RHS){
      LHS = mod(y*y + a1*y + a3);
      RHS = mod(x*x*x + a2*x*x + a4*x + a6);
      return LHS==RHS
    }
    BEGIN{
      cnt=1; # point at infinity
      for(x=0;x<p;x++) for(y=0;y<p;y++) if(eqn(x,y)) cnt++
      print cnt
    }'
}

coeffs_from_leaf(){ # prints "a1 a2 a3 a4 a6" or empty
  local leaf="$1"
  # Try: array at .curve.a
  local t; t=$(jq -r 'try (.curve.a|type) catch "null"' "$leaf") || t="null"
  if [ "$t" = "array" ]; then
    jq -r '(.curve.a | [.[0],.[1],.[2],.[3],.[4]] | @tsv) // empty' "$leaf" 2>/dev/null && return 0
  fi
  # Try: object at .curve.a.{a1..a6}
  jq -r '
    def s(v): try v catch null;
    [ s(.curve.a.a1), s(.curve.a.a2), s(.curve.a.a3), s(.curve.a.a4), s(.curve.a.a6) ]
    | select(all(. != null)) | @tsv' "$leaf" 2>/dev/null && return 0
  # Try: flat fields .curve.{a1..a6}
  jq -r '
    def s(v): try v catch null;
    [ s(.curve.a1), s(.curve.a2), s(.curve.a3), s(.curve.a4), s(.curve.a6) ]
    | select(all(. != null)) | @tsv' "$leaf" 2>/dev/null && return 0
  # Last-ditch: grep (won’t crash; may be brittle but safe)
  awk -F: '
    /"a1"\s*:/ {gsub(/[^-0-9]/,"",$2); a1=$2}
    /"a2"\s*:/ {gsub(/[^-0-9]/,"",$2); a2=$2}
    /"a3"\s*:/ {gsub(/[^-0-9]/,"",$2); a3=$2}
    /"a4"\s*:/ {gsub(/[^-0-9]/,"",$2); a4=$2}
    /"a6"\s*:/ {gsub(/[^-0-9]/,"",$2); a6=$2}
    END { if(a1""&&a2""&&a3""&&a4""&&a6"") print a1 "\t" a2 "\t" a3 "\t" a4 "\t" a6 }' "$leaf"
}

metrics="analysis/metrics/adversarial.jsonl"

# Iterate leaves; keep filenames simple
find analysis/atlas -maxdepth 2 -name leaf.json -print | sort | while IFS= read -r leaf; do
  dir=$(dirname "$leaf")
  label=$(jq -r 'try .curve.label catch "unknown"' "$leaf" 2>/dev/null || echo unknown)
  panel=$(jq -r 'try .panel.path catch ""' "$leaf" 2>/dev/null || echo "")
  [ -z "$panel" ] && { echo "[adv] $label: no panel"; continue; }
  [ -s "$panel" ] || { echo "[adv] $label: empty panel"; continue; }

  coeffs=$(coeffs_from_leaf "$leaf")
  [ -z "$coeffs" ] && { echo "[adv] $label: no coeffs"; continue; }
  a1=$(printf '%s\n' "$coeffs" | awk '{print $1}')
  a2=$(printf '%s\n' "$coeffs" | awk '{print $2}')
  a3=$(printf '%s\n' "$coeffs" | awk '{print $3}')
  a4=$(printf '%s\n' "$coeffs" | awk '{print $4}')
  a6=$(printf '%s\n' "$coeffs" | awk '{print $5}')

  nrows=$(awk 'NR>1{c++}END{print c+0}' "$panel")
  [ "$nrows" -gt 0 ] || { echo "[adv] $label: panel has no rows"; continue; }
  idx=$(pick_index "$nrows")

  read -r p ap <<EOF
$(awk -v k="$idx" 'NR>1{i++; if(i==k){print $1" "$2; exit}}' "$panel")
EOF
  [ -n "$p" ] && [ -n "$ap" ] || { echo "[adv] $label: failed to pick row"; continue; }

  npts=$(bruteforce_count "$a1" "$a2" "$a3" "$a4" "$a6" "$p")
  ap_bf=$(( p + 1 - npts ))
  verdict="fail"; [ "$ap_bf" -eq "$ap" ] && verdict="pass"

  ts=$(date -u +"%Y-%m-%dT%H:%M:%SZ")
  adv="$dir/adversarial-p${p}.json"
  jq -n --arg label "$label" --argjson p "$p" \
        --argjson ap_panel "$ap" --argjson ap_bruteforce "$ap_bf" \
        --arg verdict "$verdict" --arg ts "$ts" \
        '{label:$label, prime:$p, panel_ap:$ap_panel, brute_ap:$ap_bruteforce, verdict:$verdict, timestamp:$ts}' > "$adv"

  jq -n --arg ts "$ts" --arg label "$label" --argjson p "$p" \
        --argjson agree $([ "$verdict" = pass ] && echo 1 || echo 0) \
        --argjson ap_panel "$ap" --argjson ap_bruteforce "$ap_bf" \
        '{timestamp:$ts,label:$label,prime:$p,agree:($agree==1),panel_ap:$ap_panel,brute_ap:$ap_bruteforce}' >> "$metrics"

  echo "[adv] $label p=$p → $verdict"
done
