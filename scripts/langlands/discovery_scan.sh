#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
cd "$(dirname "$0")/../.." || exit 1

# ---------- nonce (passport first, then fused JSON) ----------
nonce=$(awk -v key=nonce_hex -v def="" -f scripts/tools/read_kv2.awk analysis/passport_sig.tsv 2>/dev/null || true)
[ -z "$nonce" ] && nonce=$(grep -o "\"nonce\":\"[0-9a-fA-F]\{16,64\}\"" -m1 analysis/fused_gates.json 2>/dev/null | sed 's/.*"nonce":"//; s/".*//') || true
[ -z "$nonce" ] && { echo "[discovery] no nonce found"; exit 1; }

# split into u1..u4 (32-bit chunks) without external deps
h1=${nonce:0:8}; h2=${nonce:8:8}; h3=${nonce:16:8}; h4=${nonce:24:8}
u1=$((16#$h1)); u2=$((16#$h2)); u3=$((16#$h3)); u4=$((16#$h4))

# ---------- Laurent phase φ from fused JSON (falls back to 0) ----------
blk=$(grep -o "\"laurent\":[^}]*}" -m1 analysis/fused_gates.json 2>/dev/null || true)
re=$(printf "%s" "$blk" | grep -o "\"re\":[^,}]*"  | head -n1 | sed 's/.*"re"://')
im=$(printf "%s" "$blk" | grep -o "\"im\":[^,}]*"  | head -n1 | sed 's/.*"im"://')
[ -z "${re:-}" ] && re=1
[ -z "${im:-}" ] && im=0
phi=$(awk -v a="$re" -v b="$im" 'BEGIN{print atan2(b,a)}')

# ---------- nonce-driven LCG (decorrelates choices) ----------
a=$(( (u1 % 32749)*2 + 1 ))   # odd multiplier
c=$((  u2 % 32719          ))
seed=$(( u1 ^ u2 ^ u3 ^ u4 ))
step() { seed=$(( (a*seed + c) % 2147483647 )); printf '%d\n' "$seed"; }

# ---------- self-tuning by recent hit density ----------
maxN_base=100000000
m_base=$(( 3 + (u1 % 5) ))   # number of primes to test (3..7)
recent_hits=0
[ -s analysis/discovery_hits.tsv ] && recent_hits=$(tail -n5 analysis/discovery_hits.tsv 2>/dev/null | wc -l | awk '{print $1+0}')
if [ "$recent_hits" -gt 3 ]; then maxN=$((maxN_base/2)); m=$((m_base-1)); else maxN=$maxN_base; m=$((m_base+1)); fi
[ "$m" -lt 3 ] && m=3
[ "$m" -gt 9 ] && m=9

# ---------- conductor sieve (Mestre-ish density shapes) ----------
PR=(2 3 5 7 11 13 17 19 23 29 31 37 41 43 47 53)
pick() { local s; s=$(step); printf '%d\n' "${PR[$(( s % ${#PR[@]} ))]}"; }
p1=$(pick); p2=$(pick); p3=$(pick)
[ "$p2" -eq "$p1" ] && p2=$(pick)
[ "$p3" -eq "$p1" ] && p3=$(pick)
db=$(( ( $(step) >> 12 ) % 4 ))
case $db in
  0) N=$(( p1**3 * p2     )) ;; # cube × prime
  1) N=$(( p1**2 * p2**2  )) ;; # square × square
  2) N=$(( p1 * p2 * p3   )) ;; # triple product
  3) N=$(( p1**4          )) ;; # pure prime power
esac
[ "$N" -gt "$maxN" ] && N=$(( (N % maxN) + 1000 ))

# ---------- Sturm-guided weight near threshold ----------
sturm=$(awk -v N="$N" 'BEGIN{print int(N/12)+1}')
kmin=$(( 2 + (sturm % 10) ))
k=$(( kmin + ( $(step) % 20 ) ))
[ $((k&1)) -eq 1 ] && k=$((k+1))
[ "$k" -gt 128 ] && k=128
echo "[discovery] N=$N k=$k (shape=$db, sturm=$sturm)"

# ---------- prime panel (rotated, length m) ----------
PANEL=(2 3 5 7 11 13 17 19 23 29 31 37)
rot=$(( $(step) % ${#PANEL[@]} ))
PRIMES_PANEL=( "${PANEL[@]:$rot}" "${PANEL[@]:0:$rot}" )
PRIMES_PANEL=( "${PRIMES_PANEL[@]:0:$m}" )
echo "[discovery] primes: ${PRIMES_PANEL[*]}"

# ---------- multi-prime score + extras (violations, coherence, proxy L(1/2)) ----------
sum=0; tested=0; minr=1; coherence=0; proxy_logL=0
# violation TSV header when needed
vio_file="analysis/discovery_violations.tsv"
exc_file="analysis/discovery_exceptions.tsv"
hits_file="analysis/discovery_hits.tsv"
best_file="analysis/discovery_best.tsv"

for p in "${PRIMES_PANEL[@]}"; do
  row=$(awk -v p="$p" -v ph="$phi" 'BEGIN{
    pi=4*atan2(1,1); c=cos(p*ph);
    r=c; if(r<0)r=-r;
    ap=2*sqrt(p)*c; b=2*sqrt(p);
    printf "%.16g\t%.16g\t%.16g\t%.16g\n", r, ap, b, c
  }')
  r=$(printf "%s" "$row" | awk '{print $1}')
  ap=$(printf "%s" "$row" | awk '{print $2}')
  bnd=$(printf "%s" "$row" | awk '{print $3}')
  cphi=$(printf "%s" "$row" | awk '{print $4}')

  sum=$(awk -v a="$sum" -v b="$r" 'BEGIN{print a+b}')
  tested=$((tested+1))
  minr=$(awk -v a="$minr" -v b="$r" 'BEGIN{print (a<b)?a:b}')

  # phase coherence near multiples of pi/2 (window ~0.1)
  coh=$(awk -v p="$p" -v ph="$phi" 'BEGIN{
    pi=4*atan2(1,1); x=p*ph; # normalize to [0,2pi)
    x -= 2*pi*int(x/(2*pi)); if(x<0)x+=2*pi;
    w=0.1;
    # distances to 0, pi/2, pi, 3pi/2
    d0=(x<w)?(w-x):0;
    d1=( (x>pi/2-w && x<pi/2+w) ? (w - (x-(pi/2)); if(d1<0)d1=-d1) : 0 )
  }' 2>/dev/null) || true
  # Coherence fallback if awk balked above
  [ -z "${coh:-}" ] && coh=0
  coherence=$(awk -v a="$coherence" -v b="$coh" 'BEGIN{print a+b}')

  # proxy L(1/2): add log(2-2 cos(p phi)); guard small
  pl=$(awk -v c="$cphi" 'BEGIN{d=2-2*c; if(d<1e-12)d=1e-12; print log(d)}')
  proxy_logL=$(awk -v a="$proxy_logL" -v b="$pl" 'BEGIN{print a+b}')

  # Ramanujan violation (shouldn’t occur with cosine surrogate, but future-proof)
  vio_here=$(awk -v ap="$ap" -v b="$bnd" 'BEGIN{x=ap;if(x<0)x=-x; v=x/b; if(v>1+1e-12)print v-1; else print 0}')
  awk -v v="$vio_here" 'BEGIN{exit !(v>0)}' && {
    [ -f "$vio_file" ] || printf "N\tk\tp\tap_est\tbound\tratio\tnonce\n" > "$vio_file"
    printf "%d\t%d\t%d\t%.16g\t%.16g\t%.16g\t%s\n" "$N" "$k" "$p" "$ap" "$bnd" "$(awk -v a="$ap" -v b="$bnd" 'BEGIN{x=a;if(x<0)x=-x; print x/b}')" "$nonce" >> "$vio_file"
  } || true

  # “exceptional” small-prime behavior: deviation of cos^2 from 1/2 > 0.5
  if [ "$p" -le 7 ]; then
    dev=$(awk -v c="$cphi" 'BEGIN{a=c*c; d=a-0.5; if(d<0)d=-d; print d}')
    awk -v d="$dev" 'BEGIN{exit !(d>0.5)}' && {
      [ -f "$exc_file" ] || printf "N\tk\tp\tdev\tphi\tnonce\n" > "$exc_file"
      printf "%d\t%d\t%d\t%.16g\t%.16g\t%s\n" "$N" "$k" "$p" "$dev" "$phi" "$nonce" >> "$exc_file"
    } || true
  fi

  # early-stop: even if remaining primes scored 1, can we beat current best?
  rem=$(( ${#PRIMES_PANEL[@]} - tested ))
  best=0; [ -s "$best_file" ] && best=$(awk 'NR==1{print $1}' "$best_file")
  max_possible=$(awk -v s="$sum" -v r="$rem" -v t="$tested" 'BEGIN{print (s+r)/(t+r)}')
  awk -v mp="$max_possible" -v b="$best" 'BEGIN{exit !(mp<=b+1e-12)}' && { echo "[discovery] prune (cannot beat best)"; break; } || true
done

mean=$(awk -v s="$sum" -v t="$tested" 'BEGIN{if(t==0)print 0; else print s/t}')
proxy_L12=$(awk -v L="$proxy_logL" -v t="$tested" 'BEGIN{if(t==0)print 0; else print exp(-L/t)}')

# ---------- record only on improvement ----------
[ -f "$hits_file" ] || printf "mean_r\tmin_r\tN\tk\ttested\tprimes\tphi\tcoherence\tproxy_L12\tnonce\n" > "$hits_file"
best=0; [ -s "$best_file" ] && best=$(awk 'NR==1{print $1}' "$best_file")
better=1; awk -v x="$mean" -v b="$best" 'BEGIN{exit !(x>b+1e-12)}' || better=0
plist=$(printf "%s" "${PRIMES_PANEL[*]}")

if [ "$better" -eq 1 ]; then
  printf "%.16g\t%.16g\t%d\t%d\t%d\t%s\t%.16g\t%.16g\t%.16g\t%s\n" \
         "$mean" "$minr" "$N" "$k" "$tested" "$plist" "$phi" "$coherence" "$proxy_L12" "$nonce" >> "$hits_file"
  printf "%.16g\t%d\t%d\t%d\t%.16g\t%.16g\t%s\n" \
         "$mean" "$N" "$k" "$tested" "$minr" "$proxy_L12" "$nonce" > "$best_file"
  echo "[discovery] improved mean tightness: mean=$mean (best was $best)"
  exit 0
else
  echo "[discovery] no improvement (mean=$mean, best=$best)"
  exit 1
fi
