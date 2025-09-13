#!/usr/bin/env bash
# lines: 49
# Stamp latest timefold meta into docs/manifest.md (idempotent section).
set -Eeuo pipefail; set +H; umask 022
root=".tau_ledger/timefolds"; man="docs/manifest.md"
[ -d "$root" ] || { echo "[err] missing $root" >&2; exit 2; }
latest="$(ls -1 "$root"/tf-*.meta 2>/dev/null | LC_ALL=C sort | tail -1 || true)"
[ -n "$latest" ] || { echo "[err] no timefold meta found" >&2; exit 2; }

# parse fields
read _ id    < <(grep '^id:'      "$latest")
read _ utc   < <(grep '^utc:'     "$latest")
read _ arc   < <(grep '^archive:' "$latest")
read _ bytes < <(grep '^bytes:'   "$latest")
read _ sha   < <(grep '^sha256:'  "$latest")
read _ files < <(grep '^files:'   "$latest")

tmp="docs/.manifest.tf.$$"; : > "$tmp"; [ -f "$man" ] || : > "$man"
# copy until our section
while IFS= read -r line; do
  case "$line" in
    "## timefold (v1)"*) break ;;
    *) printf '%s\n' "$line" >> "$tmp" ;;
  esac
done < "$man"

{
  printf '## timefold (v1)\n\n'
  printf 'id: %s\n'    "$id"
  printf 'utc: %s\n'   "$utc"
  printf 'archive: %s\n' "$arc"
  printf 'bytes: %s\n' "$bytes"
  printf 'sha256: %s\n' "$sha"
  printf 'files: %s\n' "$files"
  printf '\n'
} >> "$tmp"

mv "$tmp" "$man"
echo "[OK] manifest stamped with timefold $id (sha256:$sha)"
