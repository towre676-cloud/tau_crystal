#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
outdir=".tau_ledger/signature"; mkdir -p "$outdir"
stamp=$(date -u +%Y%m%dT%H%M%SZ); id="sigv1-$stamp"
tmp="$outdir/$id.rules.tmp"; sig="$outdir/$id.sig"; sha="$outdir/$id.sha256"
: > "$tmp"
for f in $(ls -1 constraints.d/* 2>/dev/null | LC_ALL=C sort); do
  sed -E "s/[[:space:]]+$//" "$f" | sed "/^[[:space:]]*#/d;/^[[:space:]]*$/d" >> "$tmp"
done
LC_ALL=C sort -u "$tmp" > "$sig"
scripts/meta/_sha256.sh "$sig" > "$sha"
printf "%s\n" "$sig"
