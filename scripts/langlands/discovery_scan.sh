#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
cd "$(dirname "$0")/../.." || exit 1

nonce=$(awk -v key=nonce_hex -v def="" -f scripts/tools/read_kv2.awk analysis/passport_sig.tsv 2>/dev/null || true)
[ -z "$nonce" ] && nonce=$(grep -o "\"nonce\":\"[0-9a-fA-F]\\{16,64\\}\"" -m1 analysis/fused_gates.json 2>/dev/null | sed 's/.*"nonce":"//; s/".*//' ) || true
[ -z "$nonce" ] && { echo "[discovery] no nonce found"; exit 1; }
h1=${nonce:0:16}; h2=${nonce:16:16}
u1=$(printf "%s" "$h1" | xxd -r -p 2>/dev/null | od -An -tu4 | awk "{print \$1+0}" 2>/dev/null || echo 1)
u2=$(printf "%s" "$h2" | xxd -r -p 2>/dev/null | od -An -tu4 | awk "{print \$1+0}" 2>/dev/null || echo 2)

blk=$(grep -o "\"laurent\":[^}]*}" -m1 analysis/fused_gates.json 2>/dev/null || true)
re=$(printf "%s" "$blk" | grep -o "\"re\":[^,}]*"  | head -n1 | sed 's/.*"re"://'  )
im=$(printf "%s" "$blk" | grep -o "\"im\":[^,}]*"  | head -n1 | sed 's/.*"im"://'  )
[ -z "${re:-}" ] && re=1; [ -z "${im:-}" ] && im=0
phi=$(awk -v a="$re" -v b="$im" "BEGIN{print atan2(b,a)}")

PRIMES=(2 3 5 7 11 13 17 19 23 29)
pick(){ local idx=$1 mod=$2; echo ${PRIMES[$((idx%mod))]}; }
p1=$(pick $((u1>>3)) 6); p2=$(pick $((u1>>9)) 6); [ "$p2" -eq "$p1" ] && p2=$(pick $((u1>>10)) 6)
e1=$(( 2 + (u1 & 0x1) + ((u1>>1)&0x1) ))   # 2..4
e2=$(( 2 + ((u1>>2)&0x1) ))                 # 2..3
N=$(( p1**e1 * p2**e2 ))
s1=$(pick $((u2>>3)) 10); s2=$(pick $((u2>>7)) 10); for q in "$s1" "$s2"; do [ $((N%q)) -ne 0 ] && N=$((N*q)); done
maxN=100000000   # cap to keep CI snappy
[ "$N" -gt "$maxN" ] && N=$(( (N%maxN) + 1000 ))

k=$(( 2 + (u2 % 48) )); [ $((k&1)) -eq 1 ] && k=$((k+1))
echo "[discovery] candidate level N=$N weight k=$k (seed u1=$u1 u2=$u2)"

PANEL=(2 3 5 7 11 13 17 19 23 29)
rot=$(( (u1 ^ u2) % ${#PANEL[@]} ))
PRIMES_PANEL=("${PANEL[@]:$rot}" "${PANEL[@]:0:$rot}")
m=$(( 3 + (u1 % 5) ))   # test 3..7 primes
PRIMES_PANEL=("${PRIMES_PANEL[@]:0:$m}")
echo "[discovery] testing primes: ${PRIMES_PANEL[*]}"

best=0
[ -s analysis/discovery_best.tsv ] && best=$(awk "NR==1{print \$1}" analysis/discovery_best.tsv)

sum=0; tested=0; minr=1
for p in "${PRIMES_PANEL[@]}"; do
  r=$(awk -v p="$p" -v ph="$phi" "BEGIN{c=cos(p*ph); if(c<0)c=-c; print c}")
  awk -v x="$r" "BEGIN{exit !(x==x)}" || r=0     # guard NaN
  sum=$(awk -v a="$sum" -v b="$r" "BEGIN{print a+b}")
  tested=$((tested+1))
  awk -v a="$minr" -v b="$r" "BEGIN{print (a<b)?a:b}" > .dis_min.tmp && minr=$(cat .dis_min.tmp) && rm -f .dis_min.tmp
  # early stop: even if the rest were perfect (=1), can we beat best by 1e-12?
  rem=$(( m - tested ))
  max_possible=$(awk -v s="$sum" -v r="$rem" -v t="$tested" "BEGIN{print (s+r)/(t+r)}")
  awk -v mp="$max_possible" -v b="$best" "BEGIN{exit !(mp<=b+1e-12)}" && { echo "[discovery] prune (cannot beat best)"; break; } || true
done
mean=$(awk -v s="$sum" -v t="$tested" "BEGIN{if(t==0)print 0; else print s/t}")

[ -f analysis/discovery_hits.tsv ] || printf "mean_r\tmin_r\tN\tk\ttested\tprimes\tphi\tnonce\n" > analysis/discovery_hits.tsv
better=1; awk -v x="$mean" -v b="$best" "BEGIN{exit !(x>b+1e-12)}" || better=0
plist=$(printf "%s" "${PRIMES_PANEL[*]}")
if [ "$better" -eq 1 ]; then
  printf "%.16g\t%.16g\t%d\t%d\t%d\t%s\t%.16g\t%s\n" "$mean" "$minr" "$N" "$k" "$tested" "$plist" "$phi" "$nonce" >> analysis/discovery_hits.tsv
  printf "%.16g\t%d\t%d\t%d\t%.16g\t%s\n" "$mean" "$N" "$k" "$tested" "$minr" "$nonce" > analysis/discovery_best.tsv
  echo "[discovery] improved mean tightness: mean=$mean (best was $best)"
  exit 0
else
  echo "[discovery] no improvement (mean=$mean, best=$best)"
  exit 1
fi
