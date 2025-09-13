#!/usr/bin/env bash
# lines: 38
# Stamp the interference.svg hash into manifest (idempotent section).
set -Eeuo pipefail; set +H; umask 022
man="docs/manifest.md"; svg=".tau_ledger/interf/interference.svg"
[ -f "$svg" ] || { echo "[err] no svg interference file"; exit 2; }
sha(){ scripts/meta/_sha256.sh "$1"; }
shv="$(sha "$svg")"

tmp="docs/.manifest.if.$$"; : > "$tmp"; [ -f "$man" ] || : > "$man"
while IFS= read -r line; do
  case "$line" in "## interference (v1)"*) break ;; *) printf '%s\n' "$line" >> "$tmp" ;; esac
done < "$man"
{
  printf '## interference (v1)\n\n'
  printf 'svg_path: %s\n' "$svg"
  printf 'svg_sha256: %s\n\n' "$shv"
} >> "$tmp"
mv "$tmp" "$man"
echo "[OK] interference stamp → $man (sha256:$shv)"
