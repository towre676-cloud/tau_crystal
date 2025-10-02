#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
label="${1:-11a1}"
ap1="${2:-analysis/atlas/'${label}'/ap.tsv}"
ap2="${3:-analysis/atlas/'${label}'/ap_mirror.tsv}"
atlas="analysis/atlas.jsonl"; touch "$atlas"
norm(){ awk '$1 ~ /^[0-9]+$/ && $2 ~ /^-?[0-9]+$/ {printf "%d\t%d\n",$1,$2}' "$1" | tr -d "\r"; }
tmp1=$(mktemp); tmp2=$(mktemp); norm "$ap1" > "$tmp1"; norm "$ap2" > "$tmp2"
sha1=$(scripts/meta/_sha256.sh "$tmp1"); sha2=$(scripts/meta/_sha256.sh "$tmp2")
ok=$([ "$sha1" = "$sha2" ] && echo true || echo false)
ts=$(date -u +"%Y-%m-%dT%H:%M:%SZ" 2>/dev/null || python -c "import datetime;print(datetime.datetime.utcnow().strftime(\"%Y-%m-%dT%H:%M:%SZ\"))")
out=".tau_ledger/mirror/mirror_${label}_${ts//[:]/-}.json"; : > "$out"
printf "%s\n" "{" >> "$out"
printf "%s\n" "  \"schema\":\"taucrystal/mirror_atlas/v1\"," >> "$out"
printf "%s\n" "  \"label\":\"$label\",\"sha_main\":\"$sha1\",\"sha_mirror\":\"$sha2\",\"mirror_ok\":$ok," >> "$out"
printf "%s\n" "  \"ap_main\":\"$ap1\",\"ap_mirror\":\"$ap2\",\"ts\":\"$ts\"" >> "$out"
printf "%s\n" "}" >> "$out"
printf "%s\n" "{\"type\":\"MIRROR_ATLAS\",\"label\":\"$label\",\"mirror_ok\":$ok,\"ts\":\"$ts\"}" >> "$atlas"
rm -f "$tmp1" "$tmp2"; echo "[mirror] $label mirror_ok=$ok"
