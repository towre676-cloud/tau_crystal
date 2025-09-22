#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
IMG="$1"; WIT="$2"; [ -n "$IMG" ] && [ -n "$WIT" ] || { echo "usage: $0 <image> <witness>"; exit 2; }
command -v docker >/dev/null 2>&1 || { echo "[ERR] docker missing"; exit 2; }
sha(){ if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | cut -d" " -f1; elif command -v shasum >/dev/null 2>&1; then shasum -a 256 "$1" | cut -d" " -f1; else openssl dgst -sha256 "$1" | awk "{print \$2}"; fi; }
want="sha256:$(sha "$WIT")"
have=$(docker inspect -f "{{ index .Config.Labels \"org.opencontainers.image.source.receipt\"}}" "$IMG" 2>/dev/null || true)
[ -n "$have" ] || { echo "[FAIL] label missing"; exit 1; }
[ "$have" = "$want" ] || { echo "[FAIL] label mismatch"; echo " want: $want"; echo " have: $have"; exit 1; }
echo "[OK] docker receipt label verified"
