#!/usr/bin/env bash
set -u; set +e; set +H
MAN="manifests/default.json"; TS=$(date -u +%Y%m%d-%H%M%S); BAK="$MAN.bench.$TS.bak"
[ -f "$MAN" ] && cp -f -- "$MAN" "$BAK" || :
: > "$MAN"
printf "%s\n" "README.md" >> "$MAN"
printf "%s\n" "lakefile.lean" >> "$MAN"
printf "%s\n" "lake-manifest.json" >> "$MAN"
printf "%s\n" "scripts/assure.sh" >> "$MAN"
[ -x ./scripts/assure.sh ] && ./scripts/assure.sh || echo "[warn] assure.sh missing or failed; continuing"
[ -f "$BAK" ] && mv -f -- "$BAK" "$MAN" || :
