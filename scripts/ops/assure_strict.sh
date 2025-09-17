#!/usr/bin/env bash
set -Ee -o pipefail; set +H; umask 022
sha(){ if command -v sha256sum >/dev/null 2>&1; then sha256sum | cut -d" " -f1; elif command -v shasum >/dev/null 2>&1; then shasum -a 256 | cut -d" " -f1; else openssl dgst -sha256 | awk "{print \$2}"; fi; }
root=$(git rev-parse --verify -q HEAD || echo "DIRTY")
ts=$(date -u +"%Y%m%dT%H%M%SZ")
tmp=$(mktemp) ; trap 'rm -f "$tmp"' EXIT
git ls-files -z | LC_ALL=C sort -z | while IFS= read -r -d $'\0' f; do
  [ -f "$f" ] || continue
  hn=$(cat "$f" | sha)
  printf "%s\t%s\n" "$hn" "$f" >> "$tmp"
done
[ -s "$tmp" ] || { echo "[err] no tracked files"; exit 3; }
map=$(mktemp); trap 'rm -f "$tmp" "$map"' EXIT
cp "$tmp" "$map"
printf "%s\n" "$(cut -f1 "$tmp")" > "$tmp.list"; mv "$tmp.list" "$tmp"
while :; do n=$(wc -l < "$tmp" | tr -d " "); [ "$n" -le 1 ] && break; out=$(mktemp);
  awk 'NR%2{a=$0;next}{print a$0} END{if (NR%2==1) print a$0}' "$tmp" | while IFS= read -r line; do printf "%s\n" "$line" | sha; done > "$out"
  mv "$out" "$tmp"
done
merkle=$(head -n1 "$tmp" | tr -d "\r\n")
prev=$(tail -n1 ./.tau_ledger/CHAIN 2>/dev/null | awk "{print \$1}")
elan_ver=$( (command -v elan >/dev/null 2>&1 && elan --version) || echo "none")
lake_hash=$( [ -f lake-manifest.json ] && sha256sum lake-manifest.json 2>/dev/null | cut -d" " -f1 || echo "" )
cospub=$( [ -f cosign.pub ] && tr -d "\r" < cosign.pub | tr "\n" "|" | sed 's/"/\\"/g')
rec=".tau_ledger/receipts/receipt-${ts}.json"; : > "$rec"
printf "%s\n" "{" >> "$rec"
printf "%s\n" "  \"schema\":\"taucrystal/receipt/v1\"," >> "$rec"
printf "%s\n" "  \"timestamp\":\"${ts}\"," >> "$rec"
printf "%s\n" "  \"git_head\":\"${root}\"," >> "$rec"
printf "%s\n" "  \"merkle_root\":\"${merkle}\"," >> "$rec"
printf "%s\n" "  \"prev\":\"${prev:-}\"," >> "$rec"
printf "%s\n" "  \"elan_version\":\"${elan_ver}\"," >> "$rec"
printf "%s\n" "  \"lake_manifest_hash\":\"${lake_hash}\"," >> "$rec"
printf "%s\n" "  \"cosign_pubkey\":\"${cospub}\"," >> "$rec"
printf "%s\n" "  \"files\":[" >> "$rec"
awk -F'\t' '{printf "    {\"sha\":\"%s\",\"path\":\"%s\"}%s\n",$1,$2,(NR==NR?"":",")}' "$map" >> "$rec"
printf "%s\n" "  ]" >> "$rec"
printf "%s\n" "}" >> "$rec"
rsha=$(cat "$rec" | sha)
printf "%s\t%s\n" "$rsha" "$rec" >> ./.tau_ledger/CHAIN
echo "[τ] ${root} -> ${merkle} @ ${ts} :: ${rec}"
