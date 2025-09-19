#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
cd "$(dirname "$0")/../.." || exit 1
out="${1:-analysis/arith_nonce.tsv}"
angles="analysis/satake_angles.tsv"
hecke="analysis/hecke.tsv"
mkdir -p "$(dirname "$out")"

# Prefer hecke.tsv (p, a_p) → theta = arccos(a_p/(2 sqrt p)); else use satake_angles.tsv (p, theta)
theta_min="NaN"; src="none"
if [ -s "$hecke" ]; then
  theta_min=$(awk -F"\t" 'NR>1 && $1+0>1 {p=$1+0; ap=$2+0; b=2*sqrt(p); x=ap/b; if(x>1)x=1; if(x<-1)x=-1; t=acos(x); if(min==""||t<min)min=t} END{if(min=="")print "NaN"; else printf "%.17g\n", min}' "$hecke")
  src="hecke.tsv"
elif [ -s "$angles" ]; then
  theta_min=$(awk -F"\t" 'NR>1 && $2!=""{t=$2+0; if(t<0)t=-t; if(min==""||t<min)min=t} END{if(min=="")print "NaN"; else printf "%.17g\n", min}' "$angles")
  src="satake_angles.tsv"
fi

[ "$theta_min" = "NaN" ] && { printf "theta_min\tNaN\n"; printf "gd_inv\tNaN\n"; printf "nonce_hex\t\n"; printf "source\t%s\n" "$src" > "$out"; exit 4; }

# n = gd^{-1}(theta) = ln(tan(theta/2 + pi/4))
gd_inv=$(awk -v th="$theta_min" 'BEGIN{pi=4*atan2(1,1); x=th/2.0 + pi/4.0; s=sin(x); c=cos(x); t=s/c; if(t<=0) {print "NaN"; exit} printf "%.17g\n", log(t)}')
[ "$gd_inv" = "NaN" ] && { printf "theta_min\t%s\n" "$theta_min"; printf "gd_inv\tNaN\n"; printf "nonce_hex\t\n"; printf "source\t%s\n" "$src" > "$out"; exit 4; }

# Canonicalize context string and hash → 32-byte nonce (64 hex)
ctx=$(printf "theta_min=%.17g;gd_inv=%.17g;src=%s\n" "$theta_min" "$gd_inv" "$src")
if command -v sha256sum >/dev/null 2>&1; then hex=$(printf "%s" "$ctx" | sha256sum | cut -d" " -f1);
elif command -v shasum >/dev/null 2>&1; then hex=$(printf "%s" "$ctx" | shasum -a 256 | cut -d" " -f1);
else hex=$(printf "%s" "$ctx" | openssl dgst -sha256 | awk '{print $NF}'); fi
nonce_hex=${hex:0:64}

{ printf "theta_min\t%.17g\n" "$theta_min"; printf "gd_inv\t%.17g\n" "$gd_inv"; printf "nonce_hex\t%s\n" "$nonce_hex"; printf "source\t%s\n" "$src"; } > "$out"
exit 0
