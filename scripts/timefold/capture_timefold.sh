#!/usr/bin/env bash
# lines: 57
# Capture a rewindable "timefold": archive + file list + meta.
set -Eeuo pipefail; set +H; umask 022
root=".tau_ledger/timefolds"; mkdir -p "$root"
ts="$(LC_ALL=C date -u +%Y%m%dT%H%M%SZ)"
id="tf-$ts"
lst="$root/$id.files"; meta="$root/$id.meta"; tarf="$root/$id.tar.gz"

# choose content roots (adjust as needed)
declare -a roots=( ".lake/build" "lean-toolchain" "lake-manifest.json" )
: > "$lst"
for r in "${roots[@]}"; do
  if [ -d "$r" ]; then
    LC_ALL=C find "$r" -type f -print >> "$lst"
  elif [ -f "$r" ]; then
    printf '%s\n' "$r" >> "$lst"
  fi
done
# canonicalize, no dupes
LC_ALL=C sort -u -o "$lst" "$lst"

# tar deterministically
tmpdir=".tau_ledger/.work/timefold.$$"; mkdir -p "$tmpdir"
# create a staging tree to avoid following symlinks weirdly on Windows git-bash
staging="$tmpdir/stage"; mkdir -p "$staging"
while IFS= read -r p; do
  [ -f "$p" ] || continue
  d="$staging/$(dirname "$p")"; mkdir -p "$d"
  cp -p "$p" "$staging/$p"
done < "$lst"
tar -C "$staging" --sort=name --owner=0 --group=0 --numeric-owner -czf "$tarf" .
rm -rf "$tmpdir"

sha(){ scripts/meta/_sha256.sh "$1"; }
h="$(sha "$tarf")"; bytes="$(stat -c%s "$tarf" 2>/dev/null || wc -c < "$tarf")"
: > "$meta"
printf 'id: %s\n'        "$id"     >> "$meta"
printf 'utc: %s\n'       "$ts"     >> "$meta"
printf 'archive: %s\n'   "$tarf"   >> "$meta"
printf 'bytes: %s\n'     "$bytes"  >> "$meta"
printf 'sha256: %s\n'    "$h"      >> "$meta"
printf 'files: %s\n'     "$(wc -l < "$lst" | tr -d ' ')" >> "$meta"

echo "[OK] timefold captured → $tarf (sha256:$h; files: $(wc -l < "$lst"))"
