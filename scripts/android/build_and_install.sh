#!/usr/bin/env bash
# resilient Android build/install helper for comcapsule
set -u  # (no -e so we don't bail on benign nonzero statuses)
umask 022

BASE="${BASE:-$HOME/Desktop/tau_crystal/tau_crystal}"
APP="$BASE/mobile/android/comcapsule"
PKG="io.capsule.seal"
ACT="com.capsule.MainActivity"
APK="$APP/app/build/outputs/apk/debug/app-debug.apk"
if ! command -v java >/dev/null 2>&1; then
  for d in "/c/Program Files/Android/Android Studio/jbr" "C:\Users\Cody\AppData\Local/Programs/Android Studio/jbr" "/c/Program Files/Android/Android Studio/jre" "C:\Users\Cody\AppData\Local/AndroidStudio/jbr"; do
    if [ -x "$d/bin/java.exe" ] || [ -x "$d/bin/java" ]; then export JAVA_HOME="$d"; export PATH="$JAVA_HOME/bin:$PATH"; break; fi
  done
fi

# ADB detection (Git Bash/Windows safe)
ADB="${LOCALAPPDATA:-}/Android/Sdk/platform-tools/adb.exe"
[ -x "$ADB" ] || ADB="adb"

err() { echo "[ERR] $*" >&2; }
info(){ echo "[INFO] $*"; }

require_paths() {
  [ -d "$APP" ] || { err "Android app dir missing: $APP"; return 2; }
  if [ ! -f "$APP/gradlew" ]; then
    err "gradlew not found in $APP — run Android Studio 'Generate Gradle Wrapper' or install Gradle and use 'gradle' on PATH."
    return 3
  fi
  # ensure LF endings + exec bit
  if file "$APP/gradlew" | grep -qi "CRLF"; then
    sed -i 's/\r$//' "$APP/gradlew" || true
  fi
  chmod +x "$APP/gradlew" 2>/dev/null || true
}

require_device() {
  if ! command -v "$ADB" >/dev/null 2>&1; then
    err "adb not found; install Platform Tools or add to PATH."; return 10
  fi
  # get-state fails when no device; print a friendly hint instead of exiting
  if ! "$ADB" get-state >/dev/null 2>&1; then
    err "no device detected or not authorized (adb get-state). Run: adb devices, accept the dialog, ensure USB debugging on."
    return 11
  fi
}

build() {
  require_paths || return $?
  ( cd "$APP" && ./gradlew :app:processDebugMainManifest ) || { err "processDebugMainManifest failed"; return 21; }
  local MERGED="$APP/app/build/intermediates/merged_manifests/debug/AndroidManifest.xml"
  [ -f "$MERGED" ] && { info "merged manifest:"; sed -n '1,60p' "$MERGED"; }
  ( cd "$APP" && ./gradlew :app:assembleDebug ) || { err "assembleDebug failed"; return 22; }
  [ -f "$APK" ] && ls -lh "$APK" || { err "APK missing after build: $APK"; return 23; }
  return 0
}

install_apk() {
  require_device || return $?
  [ -f "$APK" ] || { err "APK not found: $APK. Run build first."; return 31; }
  "$ADB" uninstall "$PKG" >/dev/null 2>&1 || true
  if ! "$ADB" install -r "$APK"; then
    err "adb install failed"; return 32
  fi
}

launch() {
  require_device || return $?
  info "resolve-activity check"
  if ! "$ADB" shell cmd package resolve-activity -c android.intent.category.LAUNCHER "$PKG/$ACT" >/dev/null; then
    err "Launcher not resolvable (package/class mismatch?): $PKG/$ACT"; return 41
  fi
  "$ADB" logcat -c || true
  info "am start -W $PKG/$ACT"
  "$ADB" shell am start -W -n "$PKG/$ACT" || true
}

logs() {
  require_device || return $?
  info "recent runtime lines"
  "$ADB" logcat -d -v time | grep -E "AndroidRuntime|FATAL EXCEPTION|Process: $PKG|$ACT" || echo "[OK] no crashes detected"
}

usage() {
  cat <<USAGE
Usage: $(basename "$0") [build|install|launch|logs|all]
  all     - build + install + launch + logs (default)
  build   - process merged manifest and assemble debug APK
  install - uninstall old, install fresh debug APK
  launch  - start MainActivity and wait for result
  logs    - print recent fatal/runtime lines for $PKG
USAGE
}

cmd="${1:-all}"
case "$cmd" in
  all)     build; install_apk; launch; logs ;;
  build)   build ;;
  install) install_apk ;;
  launch)  launch ;;
  logs)    logs ;;
  -h|--help) usage ;;
  *) usage; exit 1 ;;
esac

# friendly exit status summary (never “crash” on user)
echo "[DONE] $(basename "$0") $cmd"
exit 0
