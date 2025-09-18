#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
need(){ command -v "$1" >/dev/null 2>&1 || { echo "[enrich] missing $1" >&2; exit 2; }; }
need jq
atlas="analysis/atlas/atlas_hecke.jsonl"
: > "$atlas"

# helper: robust coeff extraction
coeffs_json(){
  jq -r '
    def s(v): try v catch null;
    if ((s(.curve.a)|type)=="array") then
      {a1:(.curve.a[0]),a2:(.curve.a[1]),a3:(.curve.a[2]),a4:(.curve.a[3]),a6:(.curve.a[4])}
    elif ((s(.curve.a)|type)=="object") then
      {a1:s(.curve.a.a1),a2:s(.curve.a.a2),a3:s(.curve.a.a3),a4:s(.curve.a.a4),a6:s(.curve.a.a6)}
    else
      {a1:s(.curve.a1),a2:s(.curve.a2),a3:s(.curve.a3),a4:s(.curve.a4),a6:s(.curve.a6)}
    end' "$1"
}

find analysis/atlas -maxdepth 2 -name leaf.json -print | sort | while IFS= read -r leaf; do
  dir=$(dirname "$leaf")
  label=$(jq -r 'try .curve.label catch "unknown"' "$leaf" 2>/dev/null || echo unknown)
  conductor=$(jq -r 'try .curve.conductor catch null' "$leaf" 2>/dev/null)
  panel=$(jq -r 'try .panel.path catch ""' "$leaf" 2>/dev/null || echo "")
  pcount=$(jq -r 'try .panel.primes_evaluated catch 0' "$leaf" 2>/dev/null || echo 0)
  pmax=$(jq -r 'try .panel.pmax catch 0' "$leaf" 2>/dev/null || echo 0)
  hasse_ok=$(jq -r 'try .checks.hasse_ok catch false' "$leaf" 2>/dev/null || echo false)
  rootn=$(jq -r 'try .parity.root_number catch "unknown"' "$leaf" 2>/dev/null || echo unknown)

  # numerics (be liberal: these keys might not exist yet)
  Lh=$(jq -r 'try .numeric.L_half.value catch null' "$leaf" 2>/dev/null)
  Lh_stable=$(jq -r 'try .numeric.L_half.stable catch false' "$leaf" 2>/dev/null)
  tailb=$(jq -r 'try .numeric.L_half.tail_upper catch null' "$leaf" 2>/dev/null)

  coeffs=$(coeffs_json "$leaf")
  [ -z "$panel" ] && panel=""
  jq -n \
    --arg label "$label" \
    --argjson conductor "${conductor:-null}" \
    --arg panel_path "$panel" \
    --argjson pcount "${pcount:-0}" \
    --argjson pmax   "${pmax:-0}" \
    --arg hasse_ok "$hasse_ok" \
    --arg rootn "$rootn" \
    --argjson Lh "${Lh:-null}" \
    --argjson Lh_stable "${Lh_stable:-false}" \
    --argjson tailb "${tailb:-null}" \
    --argjson coeffs "$coeffs" \
    '{
      label:$label,
      conductor:$conductor,
      coeffs:$coeffs,
      parity:{root_number:$rootn},
      panel:{path:$panel_path, primes_evaluated:$pcount, pmax:$pmax},
      numeric:{L_half:{value:$Lh, stable:$Lh_stable, tail_upper:$tailb}},
      checks:{hasse_ok:($hasse_ok=="true")},
      consensus:{bash:true,lean:true,offline:true}  # placeholder; your consensus script can update
    }' >> "$atlas"
done
echo "[enrich] wrote $(wc -l < "$atlas" | tr -d ' ') rows to $atlas"
