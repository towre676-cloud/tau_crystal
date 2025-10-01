#!/usr/bin/env bash
cd "$HOME/Desktop/tau_crystal/tau_crystal" || { echo "[err] cd failed"; }
echo "[repro] start $(date -u +%Y%m%dT%H%M%SZ 2>/dev/null || date +%Y%m%dT%H%M%S)"
SRC="/mnt/data/steel.txt"
DST="docs/specs/steel_equations.md"
echo "[repro] SRC=$SRC"; echo "[repro] DST=$DST"
[ -r "$SRC" ] && echo "[check] SRC readable" || echo "[check] SRC NOT readable"
mkdir -p "$(dirname "$DST")" || echo "[warn] mkdir failed"
TMP="$DST.tmp.$$"; echo "[repro] stage TMP=$TMP"
cp -f "$SRC" "$TMP" 2>&1; echo "[rc] cp_to_tmp=$?"
if [ -f "$DST" ]; then
  cmp -s "$TMP" "$DST"; echo "[rc] cmp=$?"
  if ! cmp -s "$TMP" "$DST"; then
    TS=$(date -u +%Y%m%dT%H%M%SZ 2>/dev/null || date +%Y%m%dT%H%M%S)
    BAK="$DST.bak.$TS"; echo "[repro] backup to $BAK"
    cp -p "$DST" "$BAK" 2>&1; echo "[rc] cp_backup=$?"
  else
    echo "[info] identical; leaving in place"; rm -f "$TMP"; echo "[rc] rm_tmp=$?";
    echo "[repro] done (no change)";
    exit 0
  fi
fi
mv -f "$TMP" "$DST" 2>&1; echo "[rc] mv=$?"
echo "[repro] end $(date -u +%Y%m%dT%H%M%SZ 2>/dev/null || date +%Y%m%dT%H%M%S)"
