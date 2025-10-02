#!/usr/bin/env bash
# Robust certificate minter: JSON with numeric h_bar
set -E -o pipefail; set +H; umask 022
global="${1:-}"; [ -f "$global" ] || { echo "usage: cert_mint.sh .tau_ledger/morpho/global.L" >&2; exit 2; }

# normalize endings
sed -i 's/\r$//' "$global" 2>/dev/null || true

# extract H_BAR and sanity-check numeric
H_BAR="$(awk -F= '/^H_BAR=/{print $2}' "$global" | head -n1)"
printf '%s' "$H_BAR" | awk 'BEGIN{ok=0} {if($0 ~ /^([+-]?[0-9]*\.?[0-9]+([eE][+-]?[0-9]+)?)$/) ok=1} END{exit ok?0:1}' \
  || { echo "mint: invalid H_BAR in $global: '$H_BAR'" >&2; exit 3; }

# collect locals sitting alongside (or anywhere in .tau_ledger/morpho)
shopt -s nullglob
mapfile -t LOCALS < <(ls -1 .tau_ledger/morpho/*.local 2>/dev/null || true)
locals_count="${#LOCALS[@]}"

# hashes
global_sha="$(sha256sum "$global" | awk '{print $1}')"
ts="$(date -u +%Y%m%dT%H%M%SZ)"
outdir="analysis/morpho/certificates"; mkdir -p "$outdir"
out="$outdir/cert_${ts}.json"

# write minified JSON with numeric h_bar
{
  printf '{'
  printf '"time":"%s",' "$ts"
  printf '"h_bar":%s,' "$H_BAR"
  printf '"locals":%s,' "$locals_count"
  printf '"global":{"path":"%s","sha256":"%s"}' "$global" "$global_sha"
  if [ "$locals_count" -gt 0 ]; then
    printf ',"locals_list":['
    first=1
    for lf in "${LOCALS[@]}"; do
      sha="$(sha256sum "$lf" | awk "{print \$1}")"
      [ $first -eq 1 ] || printf ','
      printf '{"path":"%s","sha256":"%s"}' "$lf" "$sha"
      first=0
    done
    printf ']'
  fi
  printf '}\n'
} > "$out"

echo "ok: certificate -> $out (H_BAR=$H_BAR; locals=$locals_count)"
