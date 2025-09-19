#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022

# Elliptic curve: y^2 + y = x^3 - x^2 - 10x - 20  (Cremona 11a1), conductor N=11
# For odd primes p != 11, #E(F_p) = 1 + sum_x (1 + (Δ/p)), Δ = 1 + 4r(x), r(x)=x^3 - x^2 - 10x - 20 mod p
# (1 + (Δ/p)) counts solutions of y^2 + y - r(x) ≡ 0; add 1 for the point at infinity.

is_prime() { # trial division (good enough for our p-range)
  local n=${1:?}; [ "$n" -ge 2 ] || { echo 0; return; }
  [ $((n%2)) -eq 0 ] && { [ "$n" -eq 2 ] && echo 1 || echo 0; return; }
  local d=3; while [ $((d*d)) -le "$n" ]; do
    [ $((n%d)) -eq 0 ] && { echo 0; return; }
    d=$((d+2))
  done
  echo 1
}

ap_11a1_for_p() {
  local p=${1:?}
  # skip bad primes
  [ "$p" -eq 2 ] && { echo "NA"; return; }
  [ "$p" -eq 11 ] && { echo "NA"; return; }
  [ "$(is_prime "$p")" = 1 ] || { echo "NA"; return; }
  awk -v p="$p" '
    function mod(a,m){ a%=m; if(a<0)a+=m; return a }
    function powmod(a,e,m, r){ r=1; a=mod(a,m); while(e>0){ if(e%2) r=mod(r*a,m); a=mod(a*a,m); e=int(e/2) } return r }
    function legendre(a,p, t){ a=mod(a,p); if(a==0) return 0; t=powmod(a,(p-1)/2,p); if(t==1) return 1; if(t==p-1) return -1; return 0 }
    BEGIN{
      count=1; # point at infinity
      for(x=0;x<p;x++){
        r = mod(x*x%p*(x-1)%p - 10*x - 20, p); # x^3 - x^2 - 10x - 20
        D = mod(1 + 4*r, p);
        ls = legendre(D,p); # -1,0,1
        sols = 1 + ls;      # 0,1,2 solutions for y
        count += sols;
      }
      ap = p + 1 - count;
      print ap;
    }'
}

if [[ "${1:-}" = "ap" ]]; then ap_11a1_for_p "${2:?}"; exit 0; fi
if [[ "${1:-}" = "prime" ]]; then is_prime "${2:?}"; exit 0; fi

cat <<EOF
usage:
  $(basename "$0") ap <prime>     # prints a_p or "NA" if p is bad
  $(basename "$0") prime <n>      # 1 if prime else 0
EOF
