#!/usr/bin/env bash
set -Ee -o pipefail; set +H; umask 022
src="${1:-}"; out="${2:-analysis/morpho/input/landmarks_clean.csv}"
[ -f "$src" ] || { echo "missing source"; exit 2; }
mkdir -p "$(dirname "$out")"
awk -v OFS="," '
  function stripcr(s){sub(/\r$/,"",s); return s}
  {
    line=stripcr($0)
    n=0; pos=1
    while (match(substr(line,pos), /[+-]?[0-9]*\.?[0-9]+([eE][+-]?[0-9]+)?/)) {
      tok=substr(line, pos+RSTART-1, RLENGTH)
      n++; nums[n]=tok
      pos += RSTART+RLENGTH-1
      if (n==4) break
    }
    if (n>=4) print nums[1],nums[2],nums[3],nums[4]
    delete nums
  }
' "$src" > "$out"
[ -s "$out" ] || { echo "no valid numeric rows found in $src"; exit 3; }
echo "extracted -> $out"

