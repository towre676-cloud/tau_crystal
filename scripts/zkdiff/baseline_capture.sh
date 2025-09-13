#!/usr/bin/env bash
# Capture a baseline of files: path -> sha256, plus a tree "ladder" digest.
# Usage: baseline_capture.sh [--all]  (default: tracked files only)
set -Eeuo pipefail; set +H; umask 022
include_all="${1:-}"
sha(){ scripts/meta/_sha256.sh "$1"; }
outdir=".tau_ledger/zkdiff"; mkdir -p "$outdir"
ts="$(LC_ALL=C date -u +%Y%m%dT%H%M%SZ)"
base="$outdir/base-$ts.files"
meta="$outdir/base-$ts.meta"

# enumerate files (stable, NUL‑sep)
if [ "$include_all" = "--all" ]; then
  mapfile -d '' -t files < <(git ls-files -z && git ls-files -o --exclude-standard -z)
else
  mapfile -d '' -t files < <(git ls-files -z)
fi

: > "$base"
for f in "${files[@]}"; do
  [ -f "$f" ] || continue
  h="$(sha "$f")"
  printf '%s  %s\n' "$h" "$f" >> "$base"
done
sort -o "$base" "$base"

# ladder digest over canonical listing
ladder=""
while IFS= read -r line; do
  ladder="$(printf '%s\n%s' "$ladder" "$line" | openssl dgst -sha256 | awk '{print $2}')"
done < "$base"

cnt="$(wc -l < "$base" | tr -d ' ')"
: > "$meta"
printf '%s\n' "schema: taucrystal/zkdiff-baseline/v1" >> "$meta"
printf '%s\n' "utc: $ts"                             >> "$meta"
printf '%s\n' "files: $cnt"                          >> "$meta"
printf '%s\n' "ladder_sha256: $ladder"               >> "$meta"
printf '%s\n' "listing: $(basename "$base")"         >> "$meta"

# manifest stamp (idempotent section)
man="docs/manifest.md"; tmp="docs/.manifest.zk.$$"; : > "$tmp"; [ -f "$man" ] || : > "$man"
while IFS= read -r line; do case "$line" in "## zkdiff (v1)"*) break ;; *) printf '%s\n' "$line" >> "$tmp";; esac; done < "$man"
{
  printf '%s\n' "## zkdiff (v1)"
  printf '\n'; printf '%s\n' "baseline_meta: $(basename "$meta")"
  printf '%s\n' "baseline_ladder_sha256: $ladder"
  printf '\n'
} >> "$tmp"
mv "$tmp" "$man"

echo "[OK] baseline @ $base ($cnt files) ladder=$ladder"
