#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
root=".tau_ledger/entropy"; mkdir -p "$root"
stamp=$(date -u +%Y%m%dT%H%M%SZ); id="entv1-$stamp"; json="$root/$id.json"; sha="$root/$id.sha256"
chain=".tau_ledger/CHAIN"; lines=$(wc -l < "$chain" 2>/dev/null | tr -d " " || echo 0); bytes=$(wc -c < "$chain" 2>/dev/null | tr -d " " || echo 0)
gzbytes=$(gzip -c "$chain" 2>/dev/null | wc -c | tr -d " " || echo 0)
ratio_pm=$(( (gzbytes*1000)/(bytes>0?bytes:1) ))
last2=$(tail -n 2 "$chain" 2>/dev/null | tr -d "\r")
difftag=$(printf "%s" "$last2" | awk "NR==1{a=\$0} NR==2{b=\$0} END{if(a==\"\"||b==\"\")print\"none\"; else print (a==b?\"same\":\"changed\")}")
tf_count=$(ls -1 .tau_ledger/timefolds/tf-*.tar.gz 2>/dev/null | wc -l | tr -d " ")
tf_bytes=$( { ls -1 .tau_ledger/timefolds/tf-*.tar.gz 2>/dev/null || true; } | xargs -I{} sh -c '[ -f "{}" ] && wc -c < "{}" || echo 0' | awk "{s+=\$1} END{print s+0}")
: > "$json"
printf "%s" "{" >> "$json"
printf "%s" "\"schema\":\"taucrystal/entropy/v1\"," >> "$json"
printf "%s" "\"id\":\"$id\"," >> "$json"
printf "%s" "\"utc\":\"$stamp\"," >> "$json"
printf "%s" "\"chain\":{" >> "$json"
printf "%s" "\"lines\":$lines," >> "$json"
printf "%s" "\"bytes\":$bytes," >> "$json"
printf "%s" "\"gzip_bytes\":$gzbytes," >> "$json"
printf "%s" "\"gzip_ratio_per_mille\":$ratio_pm," >> "$json"
printf "%s" "\"head_change\":\"$difftag\"" >> "$json"
printf "%s" "}," >> "$json"
printf "%s" "\"timefolds\":{" >> "$json"
printf "%s" "\"archives\":$tf_count," >> "$json"
printf "%s" "\"bytes\":$tf_bytes" >> "$json"
printf "%s" "}" >> "$json"
printf "%s\n" "}" >> "$json"
scripts/meta/_sha256.sh "$json" > "$sha"
printf "%s\n" "$json"
