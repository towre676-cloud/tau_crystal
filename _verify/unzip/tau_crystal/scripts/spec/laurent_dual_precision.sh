#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
die(){ echo "[laurent:dual] $*" >&2; exit 6; }
[ -s analysis/laurent_ring.tsv ] || die "missing analysis/laurent_ring.tsv"
read -r RE IM K_PREV Q_PREV NONCE < <(tail -n1 analysis/laurent_ring.tsv | awk '{print $1, $2, $3, $4, $5}')
[ -n "${RE:-}" ] && [ -n "${IM:-}" ] || die "bad laurent row"

round16(){ awk -v x="$1" 'BEGIN{printf "%.16g", x+0}'; }

calc_Kq_with_phi() { # args: scale, phi
  sc="$1"; phi="$2"
  bc -l <<BC
scale=0; pi=4*a(1)
define K(x){ auto a,b,t,eps; eps=10^(-60); a=1; b=sqrt(1 - x*x); while (a-b > eps){ t=(a+b)/2; b=sqrt(a*b); a=t; } return pi/(2*a) }
scale=${sc}
k=s(${phi}); Kk=K(k); Kp=K(sqrt(1-k*k)); q=e(-pi*Kp/Kk)
print Kk,"\n",q,"\n"
BC
}

# compute phi = atan2(IM,RE) robustly (bc lacks atan2); adjust quadrant
phi=$(bc -l <<BC
scale=64; pi=4*a(1)
re=$RE; im=$IM
if (re==0 && im==0){ print 0; }
else if (re==0){ if (im>0) print pi/2; else print -pi/2; }
else {
  p = a(im/re)
  if (re<0 && im>=0) p = p + pi
  if (re<0 && im<0)  p = p - pi
  print p
}
BC
)

read -r K64 Q64 < <(calc_Kq_with_phi 64 "$phi")
read -r K96 Q96 < <(calc_Kq_with_phi 96 "$phi")
K64r=$(round16 "$K64"); Q64r=$(round16 "$Q64")
K96r=$(round16 "$K96"); Q96r=$(round16 "$Q96")
KP=$(round16 "$K_PREV"); QP=$(round16 "$Q_PREV")

[ "$K64r" = "$K96r" ] || die "K(k) mismatch 64 vs 96: $K64r != $K96r"
[ "$Q64r" = "$Q96r" ] || die "q mismatch 64 vs 96: $Q64r != $Q96r"
[ "$K64r" = "$KP"   ] || die "K(k) (recalc) != stored (16d): $K64r != $KP"
[ "$Q64r" = "$QP"   ] || die "q (recalc) != stored (16d): $Q64r != $QP"

NORM=$(bc -l <<< "scale=64; ($RE*$RE)+($IM*$IM)")
DIFF=$(bc -l <<< "scale=64; if($NORM>1){$NORM-1}else{1-$NORM}")
ok=$(awk -v d="$DIFF" 'BEGIN{print (d<1e-12) ? "1" : "0"}')
[ "$ok" = "1" ] || die "|L|^2 != 1 within 1e-12 (got $NORM)"
echo "[laurent:dual] OK (K,q stable @16d; |L|≈1)"
