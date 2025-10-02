#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
ms_now(){ if command -v powershell.exe >/dev/null 2>&1; then powershell.exe -NoProfile -Command "[int64]([DateTimeOffset]::UtcNow.ToUnixTimeMilliseconds())" 2>/dev/null | tr -d "\r"; else echo $(( $(date -u +%s) * 1000 )); fi; }
sha256(){ if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | cut -d" " -f1; else openssl dgst -sha256 "$1" | awk "{print \$2}"; fi; }
json_arr_from_lines(){ # usage: json_arr_from_lines file
  f="$1"; [ -s "$f" ] || { printf "%s" "[]"; return; }
  out="["; sep=""; while IFS= read -r L; do printf -v out "%s%s\"%s\"" "$out" "$sep" "$L"; sep=","; done < "$f"; printf "%s" "$out]"; }
