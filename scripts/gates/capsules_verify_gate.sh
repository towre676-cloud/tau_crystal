#!/usr/bin/env bash
# Recompute Merkle root for each indexed capsule and compare to recorded root.
# Exits 0 if all match; 2 on any mismatch; 0 if no index exists yet.
set -euo pipefail; umask 022

idx=".tau_ledger/capsules.tsv"
[ -f "$idx" ] || { echo "[CAPVERIFY] no capsule index; skipping"; exit 0; }

# portable Merkle: hash file contents -> sorted leaves -> pairwise sha256(concat) until one
merkle_root_dir() {
  dir="$1"
  # collect leaves (sha path), excluding the receipt itself
  mapfile -t leaves < <(
    (cd "$dir" && { find . -type f ! -name 'capsule.receipt.json' -print0 | sort -z; } \
      | xargs -0 -I{} sha256sum "$dir/{}" 2>/dev/null \
      | awk -v pfx="$dir/" '{sub(pfx,"",$2); print $1"\t"$2}' \
      | LC_ALL=C sort -k2,2)
  )

  # if no files, define deterministic empty root
  if [ "${#leaves[@]}" -eq 0 ]; then
    printf "0%.0s" {1..64}
    return 0
  fi

  # start from just the hashes
  mapfile -t layer < <(printf "%s\n" "${leaves[@]}" | awk '{print $1}')
  # reduce until one hash remains
  while [ "${#layer[@]}" -gt 1 ]; do
    next=()
    i=0
    n="${#layer[@]}"
    while [ $i -lt $n ]; do
      h1="${layer[$i]}"
      if [ $((i+1)) -lt $n ]; then
        h2="${layer[$((i+1))]}"
      else
        h2="$h1"  # duplicate last if odd
      fi
      # concat two hex strings and hash
      pair="${h1}${h2}"
      root=$(printf "%s" "$pair" | xxd -r -p 2>/dev/null | sha256sum | awk '{print $1}' 2>/dev/null || \
             printf "%s" "$pair" | sha256sum | awk '{print $1}')
      next+=("$root")
      i=$((i+2))
    done
    layer=("${next[@]}")
  done
  printf "%s" "${layer[0]}"
}

rc=0
while IFS=$'\t' read -r family capsule root receipt; do
  # tolerate blank lines
  [ -n "${family:-}" ] || continue
  # receipt path is last column; capsule dir is its dirname or capsule name if relative
  if [ -n "${receipt:-}" ] && [ -f "$receipt" ]; then
    dir="$(cd "$(dirname "$receipt")" && pwd -P)"
  else
    # fallback: try to find by capsule name under analysis/capsules
    dir="$(cd "analysis/capsules/$capsule" 2>/dev/null && pwd -P || true)"
  fi
  if [ -z "${dir:-}" ] || [ ! -d "$dir" ]; then
    echo "[CAPVERIFY] missing dir for $family $capsule ($receipt)"; rc=2; continue
  fi

  # verify boundary.sig matches boundary.txt if present
  if [ -f "$dir/boundary.txt" ] && [ -f "$dir/boundary.sig" ]; then
    got=$(sha256sum "$dir/boundary.txt" | awk '{print $1}')
    want=$(awk '{print $1}' "$dir/boundary.sig")
    if [ "$got" != "$want" ]; then
      echo "[CAPVERIFY] boundary mismatch in $(basename "$dir")"; rc=2; continue
    fi
  fi

  # recompute merkle root
  recomputed="$(merkle_root_dir "$dir")"
  if [ "$recomputed" != "$root" ]; then
    echo "[CAPVERIFY] root mismatch $family $capsule recalc=$recomputed index=$root"
    rc=2; continue
  fi

  # if a receipt exists, check it contains the same root
  if [ -f "$dir/capsule.receipt.json" ]; then
    have=$(jq -r '.merkle_root // empty' "$dir/capsule.receipt.json" 2>/dev/null || true)
    if [ -n "$have" ] && [ "$have" != "$root" ]; then
      echo "[CAPVERIFY] receipt root mismatch $family $capsule receipt=$have index=$root"
      rc=2; continue
    fi
  fi

  echo "[CAPVERIFY] ok $family $capsule $root"
done < "$idx"

exit "$rc"
