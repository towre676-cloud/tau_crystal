#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022

# Paths
BASE="${BASE:-$HOME/Desktop/tau_crystal/tau_crystal}"
APP="$BASE/mobile/android/comcapsule"
PKG="io.capsule.seal"
ACT="com.capsule.MainActivity"
APK="$APP/app/build/outputs/apk/debug/app-debug.apk"

# ADB detection (Windows Git Bash friendly)
ADB="${LOCALAPPDATA:-}/Android/Sdk/platform-tools/adb.exe"
[ -x "$ADB" ] || ADB="adb"

usage() {
  cat <<USAGE
Usage: $0 [build|install|launch|logs|all]
  build   - process merged manifest and assemble debug APK
  install - uninstall old, install fresh debug APK
  launch  - start MainActivity and wait for result
  logs    - print recent fatal/runtime lines for $PKG
  all     - build + install + launch + logs (default)
USAGE
}

build() {
  cd "$APP"
  ./gradlew :app:processDebugMainManifest
  local MERGED="$APP/app/build/intermediates/merged_manifests/debug/AndroidManifest.xml"
  test -f "$MERGED" && { echo "[INFO] merged manifest at: $MERGED"; sed -n '1,60p' "$MERGED"; } || true
  ./gradlew :app:assembleDebug
  test -f "$APK" || { echo "[ERR] APK not found at $APK"; exit 2; }
  ls -lh "$APK"
}

install() {
  "$ADB" get-state
  "$ADB" uninstall "$PKG" >/dev/null 2>&1 || true
  "$ADB" install -r "$APK"
}

launch() {
  echo "[INFO] resolve-activity check"
  "$ADB" shell cmd package resolve-activity -c android.intent.category.LAUNCHER "$PKG/$ACT" || {
    echo "[ERR] Launcher not resolvable (name/package mismatch)"; exit 3; }
  "$ADB" logcat -c
  echo "[INFO] am start -W"
  "$ADB" shell am start -W -n "$PKG/$ACT" || true
}

logs() {
  echo "[INFO] recent runtime lines"
  "$ADB" logcat -d -v time | grep -E "AndroidRuntime|FATAL EXCEPTION|Process: $PKG|$ACT" || echo "[OK] no crashes detected"
}

all() { build; install; launch; logs; }

cmd="${1:-all}"
case "$cmd" in
  build|install|launch|logs|all) "$cmd" ;;
  -h|--help) usage ;;
  *) usage; exit 1 ;;
esac
