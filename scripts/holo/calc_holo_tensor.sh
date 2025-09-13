#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
outdir=".tau_ledger/holo"; stamp=$(date -u +%Y%m%dT%H%M%SZ); id="holov1-$stamp"; json="$outdir/$id.json"; sha="$outdir/$id.sha256"
mkdir -p "$outdir"
chain=".tau_ledger/CHAIN"; [ -f "$chain" ] || : > "$chain"
n_chain=$(wc -l < "$chain" | tr -d " ")
n_oleans=0; bytes_oleans=0
if [ -d .lake/build ]; then n_oleans=$(find .lake/build -type f -name ".olean" | wc -l | tr -d " "); bytes_oleans=$(find .lake/build -type f -name ".olean" -printf "%s\n" 2>/dev/null | awk "{s+=$1} END{print s+0}" 2>/dev/null || echo 0); fi
bytes_build=0; if [ -d .lake/build ]; then bytes_build=$(find .lake/build -type f -printf "%s\n" 2>/dev/null | awk "{s+=$1} END{print s+0}" 2>/dev/null || echo 0); fi
n_receipts=0; if [ -d .tau_ledger/timefolds ]; then n_receipts=$(ls -1 .tau_ledger/timefolds/tf-.meta 2>/dev/null | wc -l | tr -d " "); fi
cache_density=0
if [ "${bytes_build:-0}" -gt 0 ]; then cache_density=$(( (bytes_oleans1000)/bytes_build )); fi
exec_s=$(LC_ALL=C date -u +%s)
: > "$json"
printf "%s" "{" >> "$json"
printf "%s" ""schema":"taucrystal/holo/v1"," >> "$json"
printf "%s" ""id":"$id"," >> "$json"
printf "%s" ""utc":"$stamp"," >> "$json"
printf "%s" ""tensor":{" >> "$json"
printf "%s" ""chain_len":$n_chain," >> "$json"
printf "%s" ""oleans":$n_oleans," >> "$json"
printf "%s" ""bytes_oleans":$bytes_oleans," >> "$json"
printf "%s" ""bytes_build":$bytes_build," >> "$json"
printf "%s" ""timefold_receipts":$n_receipts," >> "$json"
printf "%s" ""cache_density_per_mille":$cache_density" >> "$json"
printf "%s" "}," >> "$json"
printf "%s" ""provenance":{" >> "$json"
printf "%s" ""exec_epoch":$exec_s" >> "$json"
printf "%s" "}" >> "$json"
printf "%s\n" "}" >> "$json"
scripts/holo/_sha256.sh "$json" > "$sha"
printf "%s\n" "$json"
