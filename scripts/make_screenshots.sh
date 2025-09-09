#!/usr/bin/env bash
set -euo pipefail
cd "$HOME/Desktop/tau_crystal/tau_crystal" || exit 1
mkdir -p media
MAGICK_BIN=""
[ -x tools/imagemagick/magick.exe ] && MAGICK_BIN="tools/imagemagick/magick.exe"
[ -z "$MAGICK_BIN" ] && command -v magick >/dev/null 2>&1 && MAGICK_BIN="$(command -v magick)"
mk_png(){
  out="$1"; shift; text="$*"; mkdir -p "$(dirname "$out")"
  if [ -n "${MAGICK_BIN:-}" ]; then
    "$MAGICK_BIN" -size 1280x720 canvas:"#0b0f1a" -gravity center -pointsize 44 -fill "#e6edf3" -annotate 0 "$text" "$out"
  elif command -v powershell.exe >/dev/null 2>&1; then
    out_win="$out"; command -v cygpath >/dev/null 2>&1 && out_win="$(cygpath -w "$out")"
    powershell.exe -NoProfile -ExecutionPolicy Bypass -File "tools/ps/draw_text.ps1" -Out "$out_win" -Text "$text"
  else
    printf "%s\n" "iVBORw0KGgoAAAANSUhEUgAAAAEAAAABCAQAAAC1HAwCAAAAC0lEQVR4nGMAAQAABQABDQottAAAAABJRU5ErkJggg==" | base64 -d > "$out"
  fi
}
mk_png media/shot-verify.png "τ-Crystal · Verify this release — cosign + sha256 proof"
mk_png media/shot-ledger.png "Ledger · CHAIN head ↔ receipt ↔ MERKLE_ROOT (machine-checkable)"
mk_png media/shot-readme.png "README · Quickstart · Verify this release · Golden diff"
echo "[shots] generated: media/shot-verify.png media/shot-ledger.png media/shot-readme.png"
