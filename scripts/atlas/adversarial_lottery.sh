#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022

pick_index(){ # deterministic from CHAIN head
  local n="$1" head; head=$(tail -n1 .tau_ledger/CHAIN | awk '{print $1}')
  local h8=${head:0:8}; printf '%d\n' $(( (16#$h8 % (n>0?n:1)) + 1 ))
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

mkdir -p analysis/metrics
metrics="analysis/metrics/adversarial.jsonl"

# Walk all curve leaves
for leaf in $(find analysis/atlas -maxdepth 2 -name leaf.json | sort); do
  dir=$(dirname "$leaf")
  label=$(jq -r '.curve.label' "$leaf")
  panel=$(jq -r '.panel.path' "$leaf")
  [ -s "$panel" ] || { echo "[adv] $label: no panel"; continue; }

  # TSV: p\t a_p ... ; pick a deterministic prime row
  nrows=$(awk 'NR>1{c++}END{print c+0}' "$panel")
  idx=$(pick_index "$nrows")
  # get p and recorded ap at that row
  read -r p ap < <(awk -v k="$idx" 'NR>1{i++; if(i==k){print $1,$2; exit}}' "$panel")

  # Curve params
  a1=$(jq -r '.curve.a[0]' "$leaf"); a2=$(jq -r '.curve.a[1]' "$leaf")
  a3=$(jq -r '.curve.a[2]' "$leaf"); a4=$(jq -r '.curve.a[3]' "$leaf"); a6=$(jq -r '.curve.a[4]' "$leaf")

  # Independent brute force recount
  npts=$(bruteforce_count "$a1" "$a2" "$a3" "$a4" "$a6" "$p")
  ap_bf=$(( p + 1 - npts ))

  ok=$([ "$ap_bf" -eq "$ap" ] && echo 1 || echo 0)
  ts=$(date -u +"%Y-%m-%dT%H:%M:%SZ")

  # Write a tiny adversarial leaf next to the curve
  adv="$dir/adversarial-p${p}.json"
  jq -n --arg label "$label" --argjson p "$p" --argjson ap_panel "$ap" \
        --argjson ap_bruteforce "$ap_bf" --arg verdict "$([ "$ok" -eq 1 ] && echo pass || echo fail)" \
        --arg ts "$ts" '{label:$label, prime:$p, panel_ap:$ap_panel, brute_ap:$ap_bruteforce, verdict:$verdict, timestamp:$ts}' > "$adv"

  # Append metrics
  jq -n --arg ts "$ts" --arg label "$label" --argjson p "$p" \
        --argjson ok "$ok" --argjson ap_panel "$ap" --argjson ap_bruteforce "$ap_bf" \
        '{timestamp:$ts,label:$label,prime:$p,agree:($ok==1),panel_ap:$ap_panel,brute_ap:$ap_bruteforce}' >> "$metrics"

  echo "[adv] $label p=$p → $( [ "$ok" -eq 1 ] && echo OK || echo MISMATCH )"
done
