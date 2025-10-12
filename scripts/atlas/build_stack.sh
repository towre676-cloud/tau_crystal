#!/usr/bin/env bash
set +H; set -euo pipefail; umask 022; export LC_ALL=C
trap 'echo "[ERROR] line $LINENO status=$?" >&2' ERR
usage(){ printf "usage: %s GEO TORSION_LIST OUT_STACK_JSON OUT_ROOT_TXT\n" "$(basename "$0")" >&2; exit 64; }
[ "${4-}" != "" ] || usage
geo="$1"; tors="$2"; out_json="$3"; out_root="$4"
sha_file(){ if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | awk "{print \$1}"; else openssl dgst -sha256 -r "$1" | awk "{print \$1}"; fi; }
sha_str(){ if command -v sha256sum >/dev/null 2>&1; then printf "%s" "$1" | sha256sum | awk "{print \$1}"; else printf "%s" "$1" | openssl dgst -sha256 -r | awk "{print \$1}"; fi; }
need(){ command -v "$1" >/dev/null 2>&1 || { printf "ERROR: missing program: %s\n" "$1" >&2; exit 127; }; }
need sort; need awk; need sed; need tr
[ -f "$tors" ] || { printf "ERROR: torsion list not found: %s\n" "$tors" >&2; exit 66; }
[ -s "$tors" ] || { printf "ERROR: torsion list is empty: %s\n" "$tors" >&2; exit 66; }
[ -x ./scripts/atlas/make_fiber.sh ] || { printf "ERROR: scripts/atlas/make_fiber.sh not executable\n" >&2; exit 67; }
dir=".tau_ledger/stack/${geo}"; mkdir -p "$dir"
tr -d "\r" < "$tors" | sed "s/#.*$//" | sed "/^[[:space:]]*$/d" | sort | uniq > "${dir}/_alphas.txt"
: > "${dir}/_leaves.txt"
while IFS= read -r alpha; do
  [ -z "$alpha" ] && continue
  tag="$(printf "%s" "$alpha" | tr -cs "A-Za-z0-9_-" "_")"
  leaf="${dir%/*}/${geo}_alpha${tag}.json"
  ./scripts/atlas/make_fiber.sh "$geo" "$alpha" "$leaf"
  printf "%s\n" "$(sha_file "$leaf")" >> "${dir}/_leaves.txt"
done < "${dir}/_alphas.txt"
sort "${dir}/_leaves.txt" -o "${dir}/_leaves.txt"
cp "${dir}/_leaves.txt" "${dir}/_lvl_0.txt"
lvl=0
root=""
while :; do
  in="${dir}/_lvl_${lvl}.txt"; out="${dir}/_lvl_$((lvl+1)).txt"; : > "$out"
  n=$(grep -c . "$in" || true)
  if [ "${n:-0}" -eq 0 ]; then root=""; break; fi
  if [ "$n" -eq 1 ]; then root="$(sed -n "1p" "$in")"; break; fi
  i=1
  while [ $i -le "$n" ]; do
    a="$(sed -n "${i}p" "$in")"; j=$((i+1))
    if [ $j -le "$n" ]; then b="$(sed -n "${j}p" "$in")"; else b="$a"; fi
    printf "%s\n" "$(sha_str "${a}${b}")" >> "$out"
    i=$((i+2))
  done
  sort "$out" -o "$out"
  lvl=$((lvl+1))
done
printf "%s\n" "$root" > "$out_root"
spec=""; if [ -x ./scripts/atlas/spec_hash.sh ]; then spec="$(./scripts/atlas/spec_hash.sh)"; fi
printf "{" > "$out_json"
printf "\"alphas\":[" >> "$out_json"; first=1; while IFS= read -r a; do [ -z "$a" ] && continue; if [ $first -eq 1 ]; then first=0; else printf "," >> "$out_json"; fi; printf "\"%s\"" "$a" >> "$out_json"; done < "${dir}/_alphas.txt"; printf "]," >> "$out_json"
printf "\"geometry\":{\"tag\":\"%s\"}," "$geo" >> "$out_json"
printf "\"leaves\":[" >> "$out_json"; first=1; while IFS= read -r h; do [ -z "$h" ] && continue; if [ $first -eq 1 ]; then first=0; else printf "," >> "$out_json"; fi; printf "\"%s\"" "$h" >> "$out_json"; done < "${dir}/_leaves.txt"; printf "]," >> "$out_json"
printf "\"merkle_root\":\"%s\"," "$root" >> "$out_json"
printf "\"procedure\":{\"spec_hash\":\"%s\",\"index\":\"3/2\",\"normalization\":\"Ell(tau,0)=chi(X)\"}}" "$spec" >> "$out_json"
