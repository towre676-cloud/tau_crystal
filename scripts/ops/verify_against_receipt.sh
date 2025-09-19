#!/usr/bin/env bash
set -Ee -o pipefail; set +H; umask 022
sha(){ if command -v sha256sum >/dev/null 2>&1; then sha256sum | cut -d" " -f1; elif command -v shasum >/dev/null 2>&1; then shasum -a 256 | cut -d" " -f1; else openssl dgst -sha256 | awk "{print \$2}"; fi; }
rec="${1:-}"
[ -n "$rec" ] || rec="$(tail -n1 .tau_ledger/CHAIN | awk "{print \$2}")"
[ -s "$rec" ] || { echo "[verify/r] missing receipt: $rec" >&2; exit 2; }
merkle=$(sed -n "s/.*\"merkle_root\":\"\\([^\"]*\\)\".*/\\1/p" "$rec")
[ -n "$merkle" ] || { echo "[verify/r] merkle missing in receipt" >&2; exit 2; }
tmp=$(mktemp); trap 'rm -f "$tmp"' EXIT
awk -F\" "/\\\"files\\\"/ , /]/ {print}" "$rec" | grep -E "\"sha\"|\"path\"" | sed "s/[ ,{}]//g" | paste - - | awk -F: '{gsub(/\"/,""); print $2"\t"$4}' > "$tmp"
[ -s "$tmp" ] || { echo "[verify/r] no files section"; exit 2; }
map=$(mktemp); trap 'rm -f "$tmp" "$map"' EXIT; cp "$tmp" "$map"
awk -F'\t' '{print $2}' "$map" | while IFS= read -r p; do [ -f "$p" ] || { echo "[verify/r] missing path: $p" >&2; exit 3; }; done
awk -F'\t' '{cmd="cat \""$2"\" |"; print cmd}' "$map" >/dev/null 2>&1 || true
awk -F'\t' '{cmd="cat \""$2"\"" ; cmd | "sha256sum 2>/dev/null"; close(cmd)}' "$map" >/dev/null 2>&1 || true
awk -F'\t' -v fail=0 '{ cmd="cat \""$2"\"" ; cmd | "sha256sum 2>/dev/null"; close(cmd) }' >/dev/null 2>&1 || true
calc=$(awk -F'\t' '{cmd="cat \""$2"\"" ; cmd | "sha256sum 2>/dev/null"; close(cmd);}' "$map" | awk '{print $1}')
printf "%s\n" "$calc" > "$tmp.calc"
mv "$tmp.calc" "$tmp"
while :; do n=$(wc -l < "$tmp" | tr -d " "); [ "$n" -le 1 ] && break; out=$(mktemp);
  awk 'NR%2{a=$0;next}{print a$0} END{if (NR%2==1) print a$0}' "$tmp" | while IFS= read -r line; do printf "%s\n" "$line" | sha; done > "$out"
  mv "$out" "$tmp"
done
top=$(head -n1 "$tmp" | tr -d "\r\n")
[ "$top" = "$merkle" ] || { echo "[verify/r] merkle mismatch: $top != $merkle" >&2; exit 2; }
echo "[ok] receipt-only verification passed: $rec"
