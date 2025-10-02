cd "$HOME/Desktop/tau_crystal/tau_crystal" || exit 1
set -euo pipefail; umask 022; export LC_ALL=C LANG=C
rec="${1:-}"; [ -n "$rec" ] || { echo "[err] usage: couple_merge.sh <receipt.json>"; exit 2; }
[ -f "$rec" ] || { echo "[err] file not found: $rec"; exit 3; }
sz=$(wc -c <"$rec" | tr -d "[:space:]")
sha=$(openssl dgst -sha256 "$rec" | awk "{print \$2}")
ts="$(date -u +%FT%TZ)"
out=".tau_ledger/seifert/${ts//:/-}_couple.json"; : > "$out"
printf "%s" "{" >> "$out"
printf "%s" "\"ts\":\"$ts\",\"source\":\"$(printf "%s" "$rec" | sed 's/\"/\047/g')\",\"bytes\":$sz,\"sha256\":\"$sha\",\"status\":\"coupled_stub\"}" >> "$out"
echo "[ok] wrote → $out"
