#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
sha(){ if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1"|awk "{print \$1}"; else openssl dgst -sha256 "$1"|awk "{print \$2}"; fi; }
sz(){ wc -c < "$1" | tr -d "[:space:]\r"; }
SRC="${1:-}"; [ -n "$SRC" ] || { echo "[err] usage: state_replay.sh STATE.json|STATE.tar.gz"; exit 64; }
MODE="tar"; JSON=""; TAR=""; REF="";
case "$SRC" in
  *.json) MODE="json"; JSON="$SRC";;
  *.tar.gz) TAR="$SRC";;
  *) echo "[err] unknown input"; exit 64;;
esac
if [ "$MODE" = "json" ]; then
  J="$(tr -d "\r\n" < "$JSON")"
  TAR="$(printf "%s" "$J" | sed -n 's/.*"state_tar":"\([^"]*\)".*/\1/p')"
  REF="$(printf "%s" "$J" | sed -n 's/.*"state_sha":"\([^"]*\)".*/\1/p')"
  [ -n "$TAR" ] || { echo "[err] state_tar missing in JSON"; exit 66; }
fi
[ -f "$TAR" ] || { echo "[err] tar not found: $TAR"; exit 66; }
CALC="$(sha "$TAR")"
if [ -n "${REF:-}" ] && [ "$REF" != "$CALC" ]; then echo "[err] tar sha mismatch: have $CALC want $REF"; exit 65; fi
RID="$(basename "$TAR" .tar.gz)"
DST=".tau_ledger/timefold/restore/$RID"; mkdir -p "$DST"
tar -xzf "$TAR" -C "$DST"
echo "[ok] restored -> $DST"
if [ "$MODE" = "json" ]; then
  echo "[check] verifying sizes, hashes, and merkle…"
  INS="$(printf "%s" "$J" | sed -n 's/.*"inputs":\[\(.*\)\].*/\1/p')"
  rest="$INS"; ok=0; miss=0; bad_sz=0; bad_sha=0
  EXP_LIST="$DST/.expected_hashes.txt"; GOT_LIST="$DST/.actual_hashes.txt"
  : > "$EXP_LIST"; : > "$GOT_LIST"
  while [[ "$rest" =~ \"path\":\"([^\"]+)\"[^}]*\"size\":([0-9]+)[^}]*\"sha256\":\"([^\"]+)\" ]]; do
    p="${BASH_REMATCH[1]}"; esz="${BASH_REMATCH[2]}"; esha="${BASH_REMATCH[3]}"
    rest="${rest#*\"sha256\":\"$esha\"}"
    if [ -f "$DST/$p" ]; then
      gsz="$(sz "$DST/$p")"; gsha="$(sha "$DST/$p")"
      if [ "$gsz" != "$esz" ]; then bad_sz=$((bad_sz+1)); echo "[size] $p got=$gsz expected=$esz"; fi
      if [ "$gsha" != "$esha" ]; then bad_sha=$((bad_sha+1)); echo "[hash] $p got=$gsha expected=$esha"; fi
      printf "%s\n" "$esha" >> "$EXP_LIST"
      printf "%s\n" "$gsha"  >> "$GOT_LIST"
      ok=$((ok+1))
    else
      miss=$((miss+1)); echo "[missing] $p"
    fi
  done
  EMERK="$(sha "$EXP_LIST")"; GMERK="$(sha "$GOT_LIST")"
  echo "[summary] ok=$ok missing=$miss bad_size=$bad_sz bad_hash=$bad_sha"
  echo "[merkle] expected=$EMERK actual=$GMERK"
  if [ "$miss" -ne 0 ] || [ "$bad_sz" -ne 0 ] || [ "$bad_sha" -ne 0 ] || [ "$EMERK" != "$GMERK" ]; then
    echo "[err] integrity check failed"; exit 65
  fi
fi
