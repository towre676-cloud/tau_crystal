#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
atlas="analysis/atlas.jsonl"; touch "$atlas"
cur=$(scripts/meta/_sha256.sh "$atlas")
prev=$( [ -f POISON ] && tr -d "\r\n" < POISON || echo "" )
[ -n "$prev" ] && [ "$prev" != "$cur" ] && { echo "[poison] TIMELINE DISTURBED: stored=$prev now=$cur"; exit 12; }
: > POISON; printf "%s\n" "$cur" > POISON
git add POISON && git commit -m "canary: update POISON to atlas head $cur" >/dev/null 2>&1 || true
echo "[poison] ok: head=$cur"
