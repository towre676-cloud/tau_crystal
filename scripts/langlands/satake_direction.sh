#!/usr/bin/env bash
set -E -o pipefail; set +H
in="${1:-.tau_ledger/langlands/ap_stable.json}"
out="analysis/satake_angles.tsv"
svg="analysis/plots/satake_polar.svg"

emit_ap_stream(){
  f="$1"
  if command -v jq >/dev/null 2>&1; then
    jq -r '.hecke_eigenvalues | to_entries[] | "\(.key) \(.value)"' "$f"
  else
    # naive JSON pull: lines like  "11": 1.732,
    sed -n 's/^[[:space:]]*"\([0-9][0-9]*\)":[[:space:]]*\([-0-9.][0-9.eE+-]*\).*/\1 \2/p' "$f"
  fi
}

[ -s "$in" ] || { echo "[satake] no input: $in"; : > "$out"; : > "$svg"; exit 0; }

emit_ap_stream "$in" | awk '
  BEGIN{
    pi=3.141592653589793; for(i=0;i<8;i++) cnt[i]=0;
  }
  function acos(x){return atan2(sqrt(1-x*x),x)}
  {
    p=$1+0; ap=$2+0; if(p<=0) next;
    twoSqrtP=2*sqrt(p); if(twoSqrtP==0) next;
    c=ap/twoSqrtP; if(c<-1) c=-1; if(c>1) c=1;
    theta=acos(c);                       # principal angle in [0,pi]
    b=int(theta*8/pi); if(b<0) b=0; if(b>7) b=7;
    cnt[b]++
  }
  END{
    for(i=0;i<8;i++){
      ang=i*pi/8.0; print i "\t" cnt[i] "\t" ang
    }
  }' > "$out"

# crude polar wedge plot (8 wedges), opacity ~ bin weight
max=0
while read -r BIN CNT ANG; do [ "$CNT" -gt "$max" ] && max="$CNT"; done < "$out"
{
  echo '<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 400 400"><g transform="translate(200,200)">'
  while read -r BIN CNT ANG; do
    # wedge radius 150
    python - "$BIN" "$CNT" "$ANG" "$max" <<'PY'
import math,sys
bin,cnt,ang,maxv = int(sys.argv[1]), float(sys.argv[2]), float(sys.argv[3]), float(sys.argv[4] or 1)
R=150.0
dx = R*math.cos(ang);  dy = R*math.sin(ang)
dx2= R*math.cos(ang+math.pi/8); dy2= R*math.sin(ang+math.pi/8)
op=0.2 + (0.8*(cnt/maxv) if maxv>0 else 0.2)
print(f'<path d="M 0,0 L {dx:.3f},{dy:.3f} A {R},{R} 0 0,1 {dx2:.3f},{dy2:.3f} Z" fill="#4e79a7" opacity="{op:.3f}"/>')
PY
  done < "$out"
  echo '</g></svg>'
} > "$svg"

echo "[satake] wrote $out and $svg"
