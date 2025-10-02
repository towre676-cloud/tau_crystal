#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
# Usage: deploy_bolt.sh [witness-dashboard-*.tar.gz]
if [ -n "$1" ]; then pack="$1"; else pack=""; fi

root="$(pwd)"
M="build/_manifest.json"
grab(){ sed -n "s/.*\"$1\":\"\([^\"]\+\)\".*/\1/p" "$M" | head -n1; }

if [ -z "$pack" ]; then
  if [ -s "$M" ]; then
    hash="$(grab build_hash)"; ts="$(grab ts)"
    [ -n "$hash" ] && [ -n "$ts" ] && pack="witness-dashboard-${ts//[:]/-}-${hash:0:12}.tar.gz"
  fi
fi

# Fallback: choose newest witness tarball in repo root
[ -n "$pack" ] || pack="$(ls -1t witness-dashboard-*.tar.gz 2>/dev/null | head -n1 || true)"

[ -n "$pack" ] && [ -s "$pack" ] || { echo "[deploy] missing $pack"; exit 5; }

if command -v bolt >/dev/null 2>&1; then
  bolt deploy "$pack" || { echo "[deploy] bolt failed"; exit 8; }
  echo "[deploy] bolt ok → $pack"
else
  mkdir -p deploy && cp -f "$pack" deploy/ && echo "[deploy] staged ./deploy/$(basename "$pack") (no bolt CLI)"
fi
