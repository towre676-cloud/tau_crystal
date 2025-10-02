#!/usr/bin/env bash
set -o pipefail; set +H; umask 022
pack="$1"
[ -f "$pack" ] || { echo "[tau_verify] usage: tau_verify.sh <witness.tar.gz>"; exit 2; }

sha256_file(){
  if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | awk '{print $1}'; return; fi
  if command -v shasum    >/dev/null 2>&1; then shasum -a 256 "$1" | awk '{print $1}'; return; fi
  openssl dgst -sha256 "$1" 2>/dev/null | awk '{print $NF}'
}

tmpd=$(mktemp -d 2>/dev/null || mktemp -d -t tverify)
tar -xzf "$pack" -C "$tmpd" || { echo "[tau_verify] not a tar.gz"; rm -rf "$tmpd"; exit 3; }
C="$tmpd/coin.json"; P="$tmpd/ap_panel.tsv"
[ -s "$C" ] || { echo "[tau_verify] coin.json missing"; rm -rf "$tmpd"; exit 4; }
[ -s "$P" ] || { echo "[tau_verify] ap_panel.tsv missing"; rm -rf "$tmpd"; exit 5; }

# Parse fixed-order JSON with awk (no jq)
label=$(awk -F'["[:,]' '{for(i=1;i<=NF;i++) if($i=="label"){print $(i+2); exit}}' "$C")
cond=$(awk  -F'[: ,"]' '{for(i=1;i<=NF;i++) if($i=="conductor"){print $(i+1); exit}}' "$C")
pmax=$(awk  -F'[: ,"]' '{for(i=1;i<=NF;i++) if($i=="pmax"){print $(i+1); exit}}' "$C")
panel_sha=$(awk -F'["[:,]' '{for(i=1;i<=NF;i++) if($i=="panel_sha256"){print $(i+2); exit}}' "$C")
tau=$(awk   -F'[: ,"]' '{for(i=1;i<=NF;i++) if($i=="tau_int"){print $(i+1); exit}}' "$C")

panel_sha_now=$(sha256_file "$P")
[ "$panel_sha_now" = "$panel_sha" ] || { echo "[tau_verify] FAIL: panel_sha mismatch"; rm -rf "$tmpd"; exit 10; }

tau_now=$(awk 'BEGIN{MOD=1000000007; have0=0; u0=1; u1=0; s=0}
{ if(NF<2) next; ap=$2; apm=((ap%MOD)+MOD)%MOD;
  if(have0==0){u1=apm; s=(u0+u1)%MOD; have0=1; next;}
  u2=( (apm*u1)%MOD - u0 )%MOD; if(u2<0) u2+=MOD;
  s=(s+u2)%MOD; u0=u1; u1=u2 }
END{print s%MOD}' "$P")

[ "$tau_now" = "$tau" ] || { echo "[tau_verify] FAIL: tau_int mismatch"; rm -rf "$tmpd"; exit 11; }

coin_sha_now=$(sha256_file "$C")
echo "[tau_verify] OK label=$label cond=$cond pmax=$pmax panel_sha=$panel_sha tau_int=$tau coin_sha=$coin_sha_now"
rm -rf "$tmpd"
