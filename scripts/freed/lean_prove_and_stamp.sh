#!/usr/bin/env bash
set -euo pipefail
set +H
umask 022
export LC_ALL=C LANG=C

LED=".tau_ledger/freed"; mkdir -p "$LED"
STAMP="$(date -u +%Y%m%dT%H%M%SZ)"
GITHEAD="$(git rev-parse --short=12 HEAD 2>/dev/null || echo unknown)"
LEANV="$(lean --version 2>/dev/null | head -n1 || echo lean-missing)"
LAKEV="$(lake --version 2>/dev/null | head -n1 || echo lake-missing)"

BUILD_OK=0
if command -v lake >/dev/null 2>&1; then
  lake build && BUILD_OK=1 || BUILD_OK=0
else
  echo "[warn] lake not found; skipping compile"
fi

HASH="unbuilt"
if [ "$BUILD_OK" = 1 ] && [ -d ".lake/build" ]; then
  LIST=$(find .lake/build -type f -name "*.olean" -print | LC_ALL=C sort)
  if [ -n "$LIST" ]; then
    HASH=$(printf "%s\n" $LIST | xargs -I{} sha256sum "{}" | awk '{print $1}' | LC_ALL=C sort | sha256sum | awk '{print $1}')
  fi
fi

OUT="$LED/lean_build_${STAMP}.json"
cat > "$OUT" <<JSON
{
  "stamp": "$STAMP",
  "git_head": "$GITHEAD",
  "lean_version": "$LEANV",
  "lake_version": "$LAKEV",
  "build_ok": $BUILD_OK,
  "olean_merkle": "$HASH",
  "modules": ["TauCrystal.Freed"],
  "theorems": [
    "Monoidal_on_Generators",
    "CechH1_vanish",
    "pullback_eq_PF",
    "pullback_eq_AGT",
    "pullback_eq_SW",
    "sigma_is_multiplicative",
    "cechH1_zero_of_equal_overlap"
  ]
}
JSON
echo "[lean] receipt → $OUT"
sed -n '1,20p' "$OUT" || true
