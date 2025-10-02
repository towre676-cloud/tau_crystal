#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022
LED=".yakfurby/ledger/chain.tsv"
[ -s "$LED" ] || { echo "[ERR] ledger empty"; exit 1; }
prev=""
ok=1
while IFS=$'\t' read -r seg combined linked ts0 ts1 nodeid; do
  calc=$(printf "%s|%s" "$prev" "$combined" | sha256sum | awk "{print \$1}")
  [ -z "$prev" ] && calc="$combined"
  if [ "$calc" != "$linked" ]; then echo "[FAIL] link mismatch at $seg"; ok=0; fi
  prev="$combined"
done < "$LED"
[ "$ok" -eq 1 ] && echo "[OK] ledger links consistent"

# optional: verify a specific capsule if provided as arg 1
if [ "${1-}" ]; then
  CAP="$1"; TMP=".yakfurby/tmp/vcap"; rm -rf "$TMP"; mkdir -p "$TMP"
  tar -xf "$CAP" -C "$TMP" || { echo "[ERR] unable to untar $CAP"; exit 1; }
  MAN=$(ls "$TMP"/*.json 2>/dev/null | head -n1)
  VID="$TMP/video.h264"; AUD="$TMP/audio.wav"; SIG="$TMP/sig.bin"
  [ -f "$VID" ] && [ -f "$AUD" ] && [ -f "$MAN" ] || { echo "[ERR] missing files in capsule"; exit 1; }
  hv=$(sha256sum "$VID" | awk "{print \$1}")
  ha=$(sha256sum "$AUD" | awk "{print \$1}")
  # naive JSON pulls (our manifest is flat and quoted)
  val(){ key="$1"; file="$2"; sed -n "s/.*\"\("$'"$key"$'"\)\":\"\([^\"]*\)\".*/\2/p" "$file" | head -n1; }
  ts0=$(val ts_start "$MAN")
  ts1=$(val ts_end "$MAN")
  rec=$(val combined_sha256 "$MAN")
  prov=$(val signature_provenance "$MAN")
  comp=$(printf "%s|%s|%s|%s" "$hv" "$ha" "$ts0" "$ts1" | sha256sum | awk "{print \$1}")
  [ "$comp" = "$rec" ] && echo "[OK] digest matches manifest" || { echo "[FAIL] digest mismatch"; ok=0; }
  if [ -f ".yakfurby/keys/ed25519.pub" ]; then
    printf "%s" "$rec" | xxd -r -p > "$TMP/d.bin"
    if command -v ssh-keygen >/dev/null 2>&1; then
      ssh-keygen -Y verify -f ".yakfurby/keys/ed25519.pub" -I test -n file -s "$SIG" -q -m raw -l - < "$TMP/d.bin" && echo "[OK] signature valid (ssh)" || { echo "[FAIL] signature invalid (ssh)"; ok=0; }
    elif command -v openssl >/dev/null 2>&1; then
      openssl pkeyutl -verify -pubin -inkey ".yakfurby/keys/ed25519.pub" -rawin -in "$TMP/d.bin" -sigfile "$SIG" >/dev/null 2>&1 && echo "[OK] signature valid (openssl)" || { echo "[WARN] openssl verify not supported for this format"; }
    else
      echo "[WARN] no verifier available; skipped signature check"
    fi
  else
    echo "[WARN] missing .yakfurby/keys/ed25519.pub; skipped signature check"
  fi
fi
