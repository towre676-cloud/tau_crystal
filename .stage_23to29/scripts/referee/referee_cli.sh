#!/usr/bin/env bash
set -o pipefail; set +H; umask 022
STRICT=0; [ "$1" = "--strict" ] && { STRICT=1; shift; }
label="${1:-}"; src="${2:-}"
j(){ printf "%s\n" "$1"; [ "$STRICT" -eq 1 ] || exit 0; exit "${2:-0}"; }
[ -n "$label" ] || j "{\"verdict\":\"FAIL\",\"summary\":\"usage: referee_cli.sh [--strict] <label> <pack|url>\",\"citation\":\"\"}" 2
sha(){ if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1"|awk "{print \$1}"; elif command -v shasum >/dev/null 2>&1; then shasum -a 256 "$1"|awk "{print \$1}"; else openssl dgst -sha256 "$1"|awk "{print \$NF}"; fi; }
tmpdir=$(mktemp -d 2>/dev/null || mktemp -d -t referee); pack="";
cleanup(){ rm -rf "$tmpdir" "$dl" 2>/dev/null || true; }; trap cleanup EXIT
case "$src" in
  http://*|https://*|ipfs://*)
    command -v curl >/dev/null 2>&1 || j "{\"verdict\":\"FAIL\",\"summary\":\"curl not available\",\"citation\":\"\"}" 4
    dl=$(mktemp); curl -fsSL "$src" -o "$dl" || j "{\"verdict\":\"FAIL\",\"summary\":\"fetch error\",\"citation\":\"\"}" 4
    pack="$dl";;
  *)
    if [ -n "$src" ]; then pack="$src"; else pack="$(ls -1t witness-"$label"-*.tar.gz deploy/witness-"$label"-*.tar.gz 2>/dev/null | head -n1)"; fi
    [ -n "$pack" ] && [ -s "$pack" ] || j "{\"verdict\":\"FAIL\",\"summary\":\"no pack found for $label\",\"citation\":\"\"}" 5;;
esac
tar -xzf "$pack" -C "$tmpdir" 2>/dev/null || j "{\"verdict\":\"FAIL\",\"summary\":\"bad archive\",\"citation\":\"$(basename "$pack")\"}" 6
[ -s "$tmpdir/coin.json" ] && [ -s "$tmpdir/ap_panel.tsv" ] || j "{\"verdict\":\"FAIL\",\"summary\":\"missing coin.json/ap_panel.tsv\",\"citation\":\"$(basename "$pack")\"}" 6
coinsha=$(sha "$tmpdir/coin.json")
if scripts/coin/tau_verify.sh "$pack" >/dev/null 2>&1; then OK=1; else OK=0; fi
ap13=$(awk '$1==13{print $2;exit}' "$tmpdir/ap_panel.tsv")
pmax=$(awk 'END{print $1}' "$tmpdir/ap_panel.tsv")
rank_est=$(tac analysis/atlas.jsonl 2>/dev/null | awk -v L="$label" '/"type":"RANK_STAMP"/ && index($0,"\"curve\":\"" L "\""){ if (match($0,/"rank_est":[ ]*[0-9]+/)){ s=substr($0,RSTART,RLENGTH); gsub(/[^0-9]/,"",s); print s; exit } }')
[ -n "$rank_est" ] || rank_est="NA"
sum="a_13=$( [ -n "$ap13" ] && echo "$ap13" || echo NA ), pmax=$( [ -n "$pmax" ] && echo "$pmax" || echo NA ), rank_est=$rank_est"
if [ "$OK" -eq 1 ]; then j "{\"verdict\":\"PASS\",\"summary\":\"$sum\",\"citation\":\"Coin:$(basename "$pack") SHA-256:$coinsha\"}" 0; else j "{\"verdict\":\"FAIL\",\"summary\":\"verification failed; $sum\",\"citation\":\"Coin:$(basename "$pack") SHA-256:$coinsha\"}" 1; fi
