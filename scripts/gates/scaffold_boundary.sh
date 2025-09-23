#!/usr/bin/env bash
set -euo pipefail; umask 022
dir="${1:?pack_dir}"
btxt="$dir/boundary.txt"; bsig="$dir/boundary.sig"
mkdir -p "$dir"
printf "#placeholder\nBoundary scaffolded UTC=%s\n" "$(date -u +%Y-%m-%dT%H:%M:%SZ)" > "$btxt"
sha=$(sha256sum "$btxt" | awk '{print $1}')
printf "%s  %s\n" "$sha" "$(basename "$btxt")" > "$bsig"
echo "[BOUNDARY] scaffolded $btxt and $bsig"
exit 0
