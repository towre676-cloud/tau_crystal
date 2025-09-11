#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022

sh_files=$(git ls-files "*.sh" 2>/dev/null || true)
fixed=0
for f in $sh_files; do
  if ! head -n 5 "$f" | grep -q "set +H"; then
    tmp="$(mktemp)";
    printf "%s\n" "#!/usr/bin/env bash"            > "$tmp"
    printf "%s\n" "set -Eeuo pipefail; set +H; umask 022" >> "$tmp"
    tail -n +1 "$f" >> "$tmp"
    mv "$tmp" "$f"; chmod +x "$f"; fixed=$((fixed+1))
  fi
  tr -d "\r" < "$f" > "$f.tmp" && mv "$f.tmp" "$f"
done
printf "%s\n" "[fix] inserted prologues where missing and normalized line endings. files touched: $fixed"
