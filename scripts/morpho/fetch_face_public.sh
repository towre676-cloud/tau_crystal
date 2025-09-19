#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
ARTURL="${1:-${ARTURL:-}}"
[ -n "$ARTURL" ] || { echo "[err] provide artifact landing URL"; exit 2; }
UA="Mozilla/5.0 (X11; Linux x86_64; rv:115.0) Gecko/20100101 Firefox/115.0"
LOC="$(curl -sI -H "User-Agent: $UA" "$ARTURL" | awk 'tolower($1)=="location:"{gsub(/\r/,"",$2); print $2; exit}')"
[ -n "$LOC" ] || { echo "[err] no redirect; URL not public or wrong"; exit 3; }
ZIP="$(mktemp 2>/dev/null || mktemp -t tmpzip)"
curl -fLsS --max-redirs 5 -H "User-Agent: $UA" -o "$ZIP" "$LOC" || { echo "[err] download failed"; rm -f "$ZIP"; exit 4; }
FACE="$(tar -tf "$ZIP" 2>/dev/null | grep -i "/FACE\.txt$" | head -n1)"
FACE2="$(tar -tf "$ZIP" 2>/dev/null | grep -i "/face2\.txt$" | head -n1)"
if [ -n "$FACE" ]; then echo "----- $FACE -----"; tar -xOf "$ZIP" "$FACE"; else echo "[warn] FACE.txt not found"; fi
if [ -n "$FACE2" ]; then echo "----- $FACE2 -----"; tar -xOf "$ZIP" "$FACE2"; else echo "[warn] face2.txt not found"; fi
echo "[candidates]"; tar -tf "$ZIP" 2>/dev/null | grep -i "face[^/]*\.txt" | sed -n "1,200p"
rm -f "$ZIP"
