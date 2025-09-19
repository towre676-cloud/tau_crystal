#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
PUB="analysis/morpho/public"; IN="analysis/morpho/input"; DECROOT="analysis/morpho/decrypted"
mkdir -p "$PUB"
sha(){ openssl dgst -sha256 "$1" | awk "{print \$2}"; }
src=""
if [ -f "$IN/FACE.txt" ] && [ -f "$IN/face2.txt" ]; then src="$IN";
else d=$(ls -1dt "$DECROOT"/decrypt_* 2>/dev/null | head -n1); [ -n "$d" ] && [ -f "$d/FACE.txt" ] && [ -f "$d/face2.txt" ] && src="$d"; fi
[ -n "$src" ] || { echo "[public-face] no FACE.txt + face2.txt found in input/ or decrypted/"; exit 2; }
cp -f "$src/FACE.txt"  "$PUB/FACE.txt"  || { echo "[public-face] copy FACE.txt failed"; exit 3; }
cp -f "$src/face2.txt" "$PUB/face2.txt" || { echo "[public-face] copy face2.txt failed"; exit 4; }
F_SHA=$(sha "$PUB/FACE.txt"); F2_SHA=$(sha "$PUB/face2.txt")
ts=$(date -u +%Y%m%d_%H%M%S); TAR="$PUB/face_public_$ts.tar"
(cd "$PUB" && tar -cf "$(basename "$TAR")" FACE.txt face2.txt) || { echo "[public-face] tar failed"; exit 5; }
TAR_SHA=$(sha "$TAR")
echo "[public-face] FACE.txt   sha256=$F_SHA"
echo "[public-face] face2.txt  sha256=$F2_SHA"
echo "[public-face] tar        $TAR (sha256=$TAR_SHA)"
echo "---------- FACE.txt ----------";  sed -n "1,200p" "$PUB/FACE.txt"
echo "---------- face2.txt ----------"; sed -n "1,200p" "$PUB/face2.txt"
