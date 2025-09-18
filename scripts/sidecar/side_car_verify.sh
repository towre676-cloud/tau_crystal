#!/usr/bin/env bash
set -o pipefail; set +H; umask 022
STRICT=0; [ "$1" = "--strict" ] && { STRICT=1; shift; }
pack="${1:-}"; verdict="FAIL"; summary="usage: side_car_verify.sh [--strict] <pack.tar.gz>"; citation=""
[ -n "$pack" ] || { echo "[sidecar] {\"verdict\":\"$verdict\",\"summary\":\"$summary\",\"citation\":\"$citation\"}"; [ "$STRICT" -eq 1 ] && false; return 0 2>/dev/null || :; }
sha(){ if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1"|awk "{print \$1}";
      elif command -v shasum >/dev/null 2>&1; then shasum -a 256 "$1"|awk "{print \$1}";
      else openssl dgst -sha256 "$1" 2>/dev/null | awk "{print \$NF}"; fi; }
tmp="$(mktemp -d 2>/dev/null || mktemp -d -t sidecar)"; trap "rm -rf \"$tmp\"" EXIT
if ! tar -tzf "$pack" >/dev/null 2>&1; then echo "[sidecar] {\"verdict\":\"FAIL\",\"summary\":\"bad archive\",\"citation\":\"\"}"; [ "$STRICT" -eq 1 ] && false; return 0 2>/dev/null || :; fi
tar -xzf "$pack" -C "$tmp" >/dev/null 2>&1 || { echo "[sidecar] {\"verdict\":\"FAIL\",\"summary\":\"extract error\",\"citation\":\"\"}"; [ "$STRICT" -eq 1 ] && false; return 0 2>/dev/null || :; }
C="$tmp/side_car.json"; P="$tmp/payload.bin"
[ -s "$C" ] && [ -s "$P" ] || { echo "[sidecar] {\"verdict\":\"FAIL\",\"summary\":\"missing side_car.json or payload.bin\",\"citation\":\"\"}"; [ "$STRICT" -eq 1 ] && false; return 0 2>/dev/null || :; }
schema=$(sed -n "s/.*\"schema\":\"\\([^\"]\\+\\)\".*/\\1/p" "$C" | head -n1)
producer=$(sed -n "s/.*\"producer\":\"\\([^\"]\\+\\)\".*/\\1/p" "$C" | head -n1)
tau_decl=$(sed -n "s/.*\"tau_int\":[ ]*\\([0-9]\\+\\).*/\\1/p" "$C" | head -n1)
sha_decl=$(sed -n "s/.*\"payload_sha256\":\"\\([^\"]\\+\\)\".*/\\1/p" "$C" | head -n1)
[ "$schema" = "side-car-v1" ] || { echo "[sidecar] {\"verdict\":\"FAIL\",\"summary\":\"wrong schema (expect side-car-v1)\",\"citation\":\"\"}"; [ \"$STRICT\" -eq 1 ] && false; return 0 2>/dev/null || :; }
sha_calc="$(sha "$P")"
[ "$sha_calc" = "$sha_decl" ] || { echo "[sidecar] {\"verdict\":\"FAIL\",\"summary\":\"payload sha mismatch\",\"citation\":\"sha=$sha_calc decl=$sha_decl\"}"; [ "$STRICT" -eq 1 ] && false; return 0 2>/dev/null || :; }
MOD=1000000007; u0=1; u1=0; s=0; have0=0; hex="$sha_calc"; len=${#hex}; i=0
while [ $i -lt $len ]; do h="${hex:i:2}"; v=$(( 16#${h} % MOD ));
  if [ $have0 -eq 0 ]; then u1=$v; s=$(( (u0+u1) % MOD )); have0=1; i=$((i+2)); continue; fi
  u2=$(( ( (v*u1) % MOD - u0 ) % MOD )); [ $u2 -lt 0 ] && u2=$((u2+MOD))
  s=$(( (s+u2) % MOD )); u0=$u1; u1=$u2; i=$((i+2));
done; tau_calc=$s
if [ "$tau_calc" = "$tau_decl" ]; then
  echo "[sidecar] {\"verdict\":\"PASS\",\"producer\":\"$producer\",\"tau_int\":$tau_calc,\"sha\":\"$sha_calc\"}"
  [ "$STRICT" -eq 1 ] && true
else
  echo "[sidecar] {\"verdict\":\"FAIL\",\"summary\":\"tau mismatch\",\"tau_calc\":$tau_calc,\"tau_decl\":$tau_decl,\"sha\":\"$sha_calc\"}"
  [ "$STRICT" -eq 1 ] && false
fi
