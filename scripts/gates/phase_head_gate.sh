#!/usr/bin/env bash
set -euo pipefail; umask 022
d=".tau_ledger/langlands"
latest="$d/phase_next_latest.sha"
[ -f "$latest" ] || { echo "[PHASE] missing $latest"; exit 2; }
bestfile="$(LC_ALL=C ls "$d"/phase_next_*.sha 2>/dev/null | grep -v latest | sort -V | tail -n1 || true)"
[ -n "$bestfile" ] || { echo "[PHASE] no phase_next_*.sha"; exit 3; }
bestbase="$(basename -- "$bestfile")"

target=""
if [ -L "$latest" ]; then
  target="$(basename -- "$(readlink "$latest")")"
else
  # accept a tiny pointer file or try to extract a token
  if [ "$(wc -c <"$latest" | tr -d ' \r\n')" -le 128 ]; then
    line="$(tr -d '\r' < "$latest" | head -n1)"
    case "$line" in phase_next_*Z.sha) target="$line" ;; esac
  fi
  [ -z "$target" ] && target="$(grep -Eo 'phase_next_[0-9]{8}_[0-9]{6}Z\.sha' "$latest" | tail -n1 || true)"
fi

if [ "$target" = "$bestbase" ]; then
  echo "[PHASE] ok latest points to $target"; exit 0
fi

printf "%s\n" "$bestbase" > "$latest"
echo "[PHASE] fixed: wrote pointer to $bestbase"
grep -q "$bestbase" "$latest" && { echo "[PHASE] ok latest points to $bestbase"; exit 0; }
echo "[PHASE] could not fix latest -> $bestbase"; exit 5
