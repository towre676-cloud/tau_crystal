#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022
out="analysis/provenance_map.tsv"; tmp="${out}.tmp"; : > "$tmp"
printf "producer\tproducer_sha\trun_argv\tenv_sha\tartifact_path\tartifact_sha\n" >> "$tmp"
sha() { sha256sum "$1" | awk "{print \$1}"; }
norm_env() { env | LC_ALL=C sort | tr -d "\r"; }
env_sha=$(norm_env | sha256sum | awk "{print \$1}")
find scripts -type f \( -name "*.sh" -o -name "*.py" -o -name "*.awk" \) | LC_ALL=C sort | while IFS= read -r p; do
  ps=$(sha "$p")
  meta="analysis/.provenance/$(echo "$p" | tr "/ " "__").artifacts"
  if [ -f "$meta" ]; then
    while IFS= read -r a; do
      [ -n "$a" ] || continue
      [ -e "$a" ] || continue
      as=$(sha "$a")
      printf "%s\t%s\t%s\t%s\t%s\t%s\n" "$p" "$ps" "argv@unknown" "$env_sha" "$a" "$as" >> "$tmp"
    done < "$meta"
  fi
done
mv "$tmp" "$out"
