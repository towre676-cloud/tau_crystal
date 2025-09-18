#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
atlas="analysis/atlas.jsonl"
built="build/data/atlas.jsonl"

# optional timeline continuity
if [ -x scripts/assure/poison_canary.sh ]; then
  scripts/assure/poison_canary.sh || { echo "[assure] poison canary failed"; exit 12; }
fi

[ -s "$atlas" ] && [ -s "$built" ] || { echo "[assure] missing atlas or build copy"; exit 4; }
a="$(scripts/meta/_sha256.sh "$atlas")"
b="$(scripts/meta/_sha256.sh "$built")"
[ "$a" = "$b" ] || { echo "[assure] atlas hash drift (repo=$a build=$b)"; exit 7; }

echo "[assure] ok: atlas=$a"
