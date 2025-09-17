set -Eeuo pipefail

# Minimal invariants and discriminant from (a1..a6). Outputs b2 b4 b6 b8 Δ
tau_invariants() {
  local a1="$1" a2="$2" a3="$3" a4="$4" a6="$5"
  # b2 = a1^2 + 4 a2
  local b2=$(( a1*a1 + 4*a2 ))
  # b4 = 2 a4 + a1 a3
  local b4=$(( 2*a4 + a1*a3 ))
  # b6 = a3^2 + 4 a6
  local b6=$(( a3*a3 + 4*a6 ))
  # b8 = a1^2 a6 + 4 a2 a6 - a1 a3 a4 + a2 a3^2 - a4^2
  local b8=$(( a1*a1*a6 + 4*a2*a6 - a1*a3*a4 + a2*a3*a3 - a4*a4 ))
  # Δ = -b2^2 b8 - 8 b4^3 - 27 b6^2 + 9 b2 b4 b6
  local delta=$(( -1*b2*b2*b8 - 8*b4*b4*b4 - 27*b6*b6 + 9*b2*b4*b6 ))
  printf "%s\t%s\t%s\t%s\t%s\n" "$b2" "$b4" "$b6" "$b8" "$delta"
}

# modular reduction (positive representative)
modp(){ local x="$1" p="$2"; x=$(( x % p )); [ "$x" -lt 0 ] && x=$((x+p)); printf "%d" "$x"; }

# fast powmod base^exp mod p (p odd prime)
powmod(){
  local base="$1" exp="$2" p="$3" res=1
  base=$(( base % p )); [ "$base" -lt 0 ] && base=$((base+p))
  while [ "$exp" -gt 0 ]; do
    if [ $((exp & 1)) -eq 1 ]; then res=$(( (res*base) % p )); fi
    base=$(( (base*base) % p ))
    exp=$(( exp >> 1 ))
  done
  printf "%d" "$res"
}

# Legendre symbol (a|p) ∈ {-1,0,1} for odd prime p
legendre(){
  local a=$(modp "$1" "$2") p="$2"
  [ "$a" -eq 0 ] && { echo 0; return; }
  local e=$(( (p-1)/2 ))
  local t=$(powmod "$a" "$e" "$p")
  case "$t" in
    1) echo 1;;
    0) echo 0;;
    *) echo -1;;
  esac
}

# count points mod p on Weierstrass y^2 + a1 x y + a3 y = x^3 + a2 x^2 + a4 x + a6 (p odd)
# returns #E(F_p) including point at infinity. Skips singular x where needed via discriminant in y.
count_points_mod_p(){
  local a1="$1" a2="$2" a3="$3" a4="$4" a6="$5" p="$6"
  local x RHS B D chi sum=0
  for ((x=0; x<p; x++)); do
    RHS=$(( ( ( (x*x % p)*x ) % p + (a2 * (x*x % p)) ) % p ))
    RHS=$(( (RHS + (a4 * x) ) % p ))
    RHS=$(( (RHS + a6) % p ))
    B=$(( (a1 * x + a3) % p ))
    D=$(( (B*B % p + (4 * (RHS % p)) ) % p ))
    [ "$D" -lt 0 ] && D=$((D+p))
    chi=$(legendre "$D" "$p")
    sum=$(( sum + 1 + chi ))   # 1 root if D=0, 2 if quadratic residue, 0 if non-residue
  done
  # add point at infinity
  printf "%d" $(( sum + 1 ))
}
