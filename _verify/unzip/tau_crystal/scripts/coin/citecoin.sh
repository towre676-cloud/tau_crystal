#!/usr/bin/env bash
set -o pipefail; set +H; umask 022
pack="$1"
[ -f "$pack" ] || { echo "usage: citecoin.sh <witness.tar.gz>" >&2; exit 2; }

sha256_file(){
  if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | awk '{print $1}'; return; fi
  if command -v shasum    >/dev/null 2>&1; then shasum -a 256 "$1" | awk '{print $1}'; return; fi
  openssl dgst -sha256 "$1" 2>/dev/null | awk '{print $NF}'
}

tmpd=$(mktemp -d 2>/dev/null || mktemp -d -t tcite)
tar -xzf "$pack" -C "$tmpd" || { echo "bad pack" >&2; rm -rf "$tmpd"; exit 3; }
C="$tmpd/coin.json"
[ -s "$C" ] || { echo "coin.json missing" >&2; rm -rf "$tmpd"; exit 4; }

coin_sha=$(sha256_file "$C")
label=$(awk -F'["[:,]' '{for(i=1;i<=NF;i++) if($i=="label"){print $(i+2); exit}}' "$C")
ts=$(awk    -F'["[:,]' '{for(i=1;i<=NF;i++) if($i=="ts"){print $(i+2); exit}}' "$C")
short=${coin_sha:0:12}
printf "\\\\citecoin{%s}{%s}{%s}\n" "$label" "$ts" "$short"
rm -rf "$tmpd"
