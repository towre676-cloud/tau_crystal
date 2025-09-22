#!/usr/bin/env bash
set -euo pipefail; umask 022
d=".tau_ledger/langlands"
latest="$d/phase_next_latest.sha"
[ -f "$latest" ] || { echo "[PHASE] missing $latest"; exit 2; }

# extract the intended target filename from latest:
# 1) if symlink, readlink; 2) else first/last token that matches phase_next_*.sha; 3) else empty
get_target_from_latest() {
  if [ -L "$latest" ]; then
    bn="$(basename -- "$(readlink "$latest")")"
    printf "%s" "$bn"
    return
  fi
  # try to grep a token like "phase_next_YYYYmmdd_HHMMSSZ.sha"
  tok="$(grep -Eo 'phase_next_[0-9]{8}_[0-9]{6}Z\.sha' "$latest" | tail -n1 || true)"
  if [ -n "$tok" ]; then printf "%s" "$tok"; return; fi
  # fallback: empty
  printf ""
}

target="$(get_target_from_latest)"
# compute the lexicographically newest phase file present
bestfile="$(LC_ALL=C ls "$d"/phase_next_*.sha 2>/dev/null | grep -v 'latest' | sort -V | tail -n1 || true)"
[ -n "$bestfile" ] || { echo "[PHASE] no phase_next_*.sha"; exit 3; }
bestbase="$(basename -- "$bestfile")"

if [ -z "$target" ]; then
  echo "[PHASE] latest does not name a phase_next file; suggest: ln -sf \"$bestbase\" \"$latest\""
  exit 4
fi

if [ "$target" = "$bestbase" ]; then
  echo "[PHASE] ok latest points to $target"
  exit 0
else
  echo "[PHASE] mismatch: latest points to $target but head is $bestbase"
  echo "        fix: (cd $d && ln -sf \"$bestbase\" phase_next_latest.sha)"
  exit 5
fi
