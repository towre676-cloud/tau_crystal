#!/usr/bin/env bash
set -euo pipefail
set +H
here="$(cd "$(dirname "$0")/../.." && pwd)"
out="$here/_fusion_out"
mkdir -p "$out/plumbing" "$out/spectral" "$out/tmp"
sha(){ if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1"|awk "{print \$1}"; else shasum -a 256 "$1"|awk "{print \$1}"; fi; }
ts(){ date -u +%Y-%m-%dT%H:%M:%SZ; }
printf "[plumbing] running...\\n"
bash "$here/scripts/plumbing/run_demo.sh" box-FUSE-D23 -23 1
pdir="$here/.tau_ledger/hysteresis/box-FUSE-D23"
if [ -d "$pdir" ]; then cp -rp "$pdir" "$out/plumbing/"; fi
printf "[spectral] running...\\n"
sk="$here/spectral_kernel"
if [ -d "$sk" ]; then ( cd "$sk" && if command -v lake >/dev/null 2>&1; then lake update && lake build && lake env lean --run Src/Spectral/plumbing.lean > trace.json; fi; ); fi
if [ -f "$sk/trace.json" ]; then cp -p "$sk/trace.json" "$out/spectral/trace.json"; fi
man="$out/MANIFEST.json"; : > "$man"
printf "{\\n" >> "$man"
printf "  \\"created_at\\": \\"%s\\",\\n" "$(ts)" >> "$man"
printf "  \\"files\\": [\\n" >> "$man"
first=1
while IFS= read -r -d "" fpath; do
  rel="${fpath#"$out/"}"; sum="$(sha "$fpath")"; bytes=$(wc -c < "$fpath" | tr -d " ")
  [ $first -eq 0 ] && printf ",\\n" >> "$man"; first=0
  printf "    {\\"path\\": \\"%s\\", \\"sha256\\": \\"%s\\", \\"bytes\\": %s}" "$rel" "$sum" "$bytes" >> "$man"
done < <(find "$out" -type f ! -name "MANIFEST.json" -print0 | sort -z)
printf "\\n  ]\\n}\\n" >> "$man"
printf "[fusion] wrote %s\\n" "$man"
