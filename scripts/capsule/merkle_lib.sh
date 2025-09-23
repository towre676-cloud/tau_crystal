# merkle_lib.sh — canonical Merkle routines (bash/coreutils)
# Rules:
#  • include every file under the capsule dir EXCEPT 'capsule.receipt.json'
#  • leaf = sha256(file contents), path relative to capsule dir (no leading './')
#  • order leaves by LC_ALL=C path sort
#  • reduction: if odd, duplicate last; node = sha256(rawbytes(hex(h1)||hex(h2)))
#  • hex digests are lowercase; if xxd missing, fall back to hashing the hex text (as long as both sides do it).

merkle__leaf_list() {
  local dir="$1"
  (
    cd "$dir"
    LC_ALL=C find . -type f ! -name 'capsule.receipt.json' -print0 \
      | LC_ALL=C sort -z \
      | xargs -0 -I{} sh -c '
          p="{}"; case "$p" in ./*) p="${p#./}";; esac
          sha256sum "$p" | awk -v rel="$p" "{print \$1\"\t\"rel}"
        '
  ) | LC_ALL=C sort -k2,2
}

merkle__reduce_from_hashes() {
  local -a layer next
  mapfile -t layer < <(awk 'NF{print $1}')
  if [ "${#layer[@]}" -eq 0 ]; then printf '0%.0s' {1..64}; return 0; fi
  while [ "${#layer[@]}" -gt 1 ]; do
    next=(); local i=0 n="${#layer[@]}"
    while [ $i -lt $n ]; do
      local h1="${layer[$i]}"; local h2
      if [ $((i+1)) -lt $n ]; then h2="${layer[$((i+1))]}"; else h2="$h1"; fi
      if command -v xxd >/dev/null 2>&1; then
        root="$(printf "%s%s" "$h1" "$h2" | xxd -r -p | sha256sum | awk '{print $1}')"
      else
        root="$(printf "%s%s" "$h1" "$h2" | sha256sum | awk '{print $1}')"
      fi
      next+=("$root"); i=$((i+2))
    done
    layer=("${next[@]}")
  done
  printf "%s" "${layer[0]}"
}

merkle__dir_root() {
  local dir="$1"
  mapfile -t _leaves < <(merkle__leaf_list "$dir" | awk '{print $1}')
  printf "%s\n" "${_leaves[@]}" | merkle__reduce_from_hashes
}

merkle__explain() {
  local dir="$1"
  echo "[MERKLE] leaves for $(basename "$dir"):"
  merkle__leaf_list "$dir"
  printf "[MERKLE] root: "; merkle__dir_root "$dir"; echo
}
