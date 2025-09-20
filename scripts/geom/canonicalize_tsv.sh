#!/usr/bin/env bash
set -Ee -o pipefail; set +H; umask 022
in="${1:-}"; out="${2:-/dev/stdout}"
[ -f "$in" ] || { echo "missing input TSV" >&2; exit 1; }
awk -v OFS="\t" '
  NF>=2 { xs[++n]=$1; ys[n]=$2; sx+=$1; sy+=$2; sxx+=$1*$1; syy+=$2*$2 }
  END {
    if (n==0) { exit 2 }
    mx=sx/n; my=sy/n;
    rx=sqrt(sxx/n - mx*mx); ry=sqrt(syy/n - my*my);
    if (rx==0) rx=1; if (ry==0) ry=1;
    for(i=1;i<=n;i++){ printf "%0.9f\t%0.9f\n", (xs[i]-mx)/rx, (ys[i]-my)/ry }
  }
' "$in" > "$out"
