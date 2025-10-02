cd "$HOME/Desktop/tau_crystal/tau_crystal" || exit 1
set -euo pipefail; umask 022; export LC_ALL=C LANG=C
label="${1:-}"
sha="$(git rev-parse --verify HEAD 2>/dev/null || printf "%s" none)"
branch="$(git rev-parse --abbrev-ref HEAD 2>/dev/null || printf "%s" none)"
dirty="false"; git diff --quiet --ignore-submodules -- || dirty="true"
ts="$(date -u +%FT%TZ)"
tmp=".tmp.timefold.$$"; : > "$tmp"
git ls-files -z | tr -d "\r" | xargs -0 cat 2>/dev/null | openssl dgst -sha256 -binary > "$tmp" || true
tree_sha="$(openssl dgst -sha256 "$tmp" | awk "{print \$2}")"
rm -f "$tmp"
count_files=$(git ls-files | wc -l | tr -d "[:space:]")
out=".tau_ledger/timefold/${ts//:/-}_snapshot.json"; : > "$out"
printf "%s" "{" >> "$out"
printf "%s" "\"ts\":\"$ts\",\"label\":\"$(printf "%s" "$label" | sed 's/\"/\047/g')\",\"git_sha\":\"$sha\",\"branch\":\"$branch\",\"dirty\":\"$dirty\",\"tree_sha256\":\"$tree_sha\",\"file_count\":$count_files}" >> "$out"
echo "[ok] snapshot → $out"
