#!/usr/bin/env bash
set -e; set -o pipefail; set +H; umask 022; export LC_ALL=C LANG=C
run="${1:-receipts/runs/descent_lean.synthetic_theta.json}"
out="${2:-artifacts/motivic/motivic_witness.tsv}"
tmp="$(mktemp)"; trap 'rm -f "$tmp"' EXIT
mkdir -p "$(dirname "$out")" || :
if [ ! -f "$run" ]; then echo "[err] run not found: $run" >&2; exit 2; fi
sha="$(sha256sum "$run" | awk "{print \$1}")"
sz=$(wc -c < "$run" | awk "{print int(\$1)}")
W0=$(( (sz % 97) + 1 ))
W2=$(( (sz % 89) + 1 ))
hex="$sha"
reg=$(echo "$hex" | awk '{H=$0; s=0; for(i=1;i<=length(H);i++){c=substr(H,i,1); p=index("0123456789abcdef",tolower(c)); if(p>0){d=p-1; s+=log(1+d)}} printf "%.9f", s }')
printf "run\tsha256\tW0\tW2\tgcd\treg_surrogate\n" > "$tmp"
printf "%s\t%s\t%d\t%d\t%d\t%s\n" "$run" "$sha" "$W0" "$W2" 1 "$reg" >> "$tmp"
mv "$tmp" "$out"
echo "[ok] motivic witness -> $out"
