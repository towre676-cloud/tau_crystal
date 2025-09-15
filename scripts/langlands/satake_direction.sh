#!/usr/bin/env bash
set -E -o pipefail; set +H
in="${1:-.tau_ledger/langlands/ap_stable.json}"
out="analysis/satake_angles.tsv"
svg="analysis/plots/satake_polar.svg"
emit_ap(){ if command -v jq >/dev/null 2>&1; then jq -r '.hecke_eigenvalues|to_entries[]|"\(.key) \(.value)"' "$1"; else sed -n 's/^[[:space:]]*"\([0-9]\+\)":[[:space:]]*\([-0-9.][0-9.eE+-]*\).*/\1 \2/p' "$1"; fi; }
[ -s "$in" ] || { echo "[satake] no input: $in"; : > "$out"; : > "$svg"; exit 0; }
emit_ap "$in" | awk '
  BEGIN{pi=3.141592653589793; for(i=0;i<8;i++) cnt[i]=0}
  function acos(x){return atan2(sqrt(1-x*x),x)}
  {p=$1+0; ap=$2+0; if(p<=0) next; two=2*sqrt(p); if(two==0) next;
   c=ap/two; if(c<-1)c=-1; if(c>1)c=1; theta=acos(c); b=int(theta*8/pi); if(b<0)b=0; if(b>7)b=7; cnt[b]++}
  END{for(i=0;i<8;i++) printf "%d\t%d\t%f\n", i, cnt[i], i*pi/8.0}' > "$out"
max=0; while read -r B C A; do [ "$C" -gt "$max" ] && max="$C"; done < "$out"
{
  echo '<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 400 400"><g transform="translate(200,200)">'
  while read -r B C A; do
    python - "$B" "$C" "$A" "$max" <<'PY'
import math,sys
b,c,a,m = int(sys.argv[1]), float(sys.argv[2]), float(sys.argv[3]), float(sys.argv[4] or 1)
R=150.0; dx=R*math.cos(a); dy=R*math.sin(a); dx2=R*math.cos(a+math.pi/8); dy2=R*math.sin(a+math.pi/8)
op=0.2 + (0.8*(c/m) if m>0 else 0.2)
print(f'<path d="M 0,0 L {dx:.3f},{dy:.3f} A {R},{R} 0 0,1 {dx2:.3f},{dy2:.3f} Z" fill="#4e79a7" opacity="{op:.3f}"/>')
PY
  done < "$out"
  echo '</g></svg>'
} > "$svg"
echo "[satake] wrote $out and $svg"
