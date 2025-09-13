#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
outdir=".tau_ledger/signature"; mkdir -p "$outdir"
a="${1:?usage: compose_signatures.sh <sigA> <sigB>}"
b="${2:?usage: compose_signatures.sh <sigA> <sigB>}"
stamp=$(date -u +%Y%m%dT%H%M%SZ); id="sigv1-$stamp-composed"; tmp="$outdir/$id.tmp"; sig="$outdir/$id.sig"; sha="$outdir/$id.sha256"
: > "$tmp"; cat "$a" "$b" >> "$tmp"
LC_ALL=C sort -u "$tmp" > "$sig"
scripts/meta/_sha256.sh "$sig" > "$sha"
printf "%s\n" "$sig"
