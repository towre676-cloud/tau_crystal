#!/usr/bin/env bash
set -euo pipefail

# --- Config ---
ADB="${LOCALAPPDATA}/Android/Sdk/platform-tools/adb.exe"
PKG="io.capsule.seal"
ACT="com.capsule.MainActivity"
FILTER_EXPR='ZipFlow|AndroidRuntime|FATAL EXCEPTION|Caused by:|Exception|Error|SecurityException|FileNotFoundException|Permission|denied|zip|Zip|archive|content://|FileUriExposed'

# --- Sanity ---
[ -x "$ADB" ] || { echo "adb not found at: $ADB"; exit 1; }

# Avoid MSYS path conversion on adb args (important on Git Bash)
export MSYS2_ARG_CONV_EXCL='*'

# --- Bring app to foreground (optional) ---
"$ADB" shell am start -n "$PKG/$ACT" >/dev/null 2>&1 || true

# --- Capture window ---
TS=$(date -u +%Y%m%dT%H%M%SZ)
RAW="$HOME/zipflow_${TS}.raw.log"
NORM="$HOME/zipflow_${TS}.norm.log"
SLICE="$HOME/zipflow_${TS}.slice.log"

"$ADB" logcat -c
"$ADB" logcat -b main,system,events,crash,radio,default -v time > "$RAW" &
LPID=$!

echo ">>> Reproduce the ZIP flow now (you have ~45s) <<<"
sleep 45

# stop capture
kill "$LPID" 2>/dev/null || true
wait "$LPID" 2>/dev/null || true

# normalize + slice
tr -d '\r' < "$RAW" > "$NORM"
egrep -n "$FILTER_EXPR" "$NORM" > "$SLICE" || true

if [ ! -s "$SLICE" ]; then
  echo "[note] no hits; showing first 200 lines:"
  sed -n '1,200p' "$NORM"
else
  echo "[slice] first 200 matches:"
  sed -n '1,200p' "$SLICE"
fi

# show extraction target
APP_BOX="/sdcard/Android/data/${PKG}/files/extract_test"
"$ADB" shell "ls -l \"$APP_BOX\" 2>/dev/null || echo 'extract_test is empty or missing'"

echo
echo "[files]"
echo "RAW  : $RAW"
echo "NORM : $NORM"
echo "SLICE: $SLICE"
