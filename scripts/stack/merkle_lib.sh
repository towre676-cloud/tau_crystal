#!/usr/bin/env bash
set -euo pipefail
set +H
export LC_ALL=C

sha256_text(){
  if command -v sha256sum >/dev/null 2>&1; then printf %s "$1" | sha256sum | awk "{print \$1}"; else printf %s "$1" | openssl dgst -sha256 -r | awk "{print \$1}"; fi
}

sha256_bytes(){
  if command -v sha256sum >/dev/null 2>&1; then sha256sum | awk "{print \$1}"; else openssl dgst -sha256 -r | awk "{print \$1}"; fi
}

hexpair_hash(){
  # hash(HL || HR) with binary concatenation if xxd is available; else fall back to ascii-cat and record mode
  local hl="$1" hr="$2"
  if command -v xxd >/dev/null 2>&1; then
    printf "%s%s" "$hl" "$hr" | xxd -r -p | sha256_bytes
  else
    sha256_text "${hl}${hr}"
  fi
}

merkle_root_from_file(){
  # $1: file with one 64-hex digest per line, set-style root (sort at each level), duplicate last at odd width.
  local f="$1"
  sed -E "s/\r$//" "$f" | grep -E "^[0-9a-f]{64}$" | sort -u > "$f.leaves"
  while :; do
    set +e; readarray -t A < "$f.leaves"; set -e
    [ "${#A[@]}" -gt 0 ] || { printf "\n"; return 0; }
    [ "${#A[@]}" -eq 1 ] && { printf "%s\n" "${A[0]}"; return 0; }
    : > "$f.next"
    i=0; n=${#A[@]}
    while [ $i -lt $n ]; do
      if [ $((i+1)) -lt $n ]; then h="$(hexpair_hash "${A[$i]}" "${A[$((i+1))]}")"; else h="$(hexpair_hash "${A[$i]}" "${A[$i]}")"; fi
      printf "%s\n" "$h" >> "$f.next"
      i=$((i+2))
    done
    sort -u "$f.next" > "$f.leaves"
  done

