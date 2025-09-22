set -Eeuo pipefail

tau_invariants() {
  local a1="$1" a2="$2" a3="$3" a4="$4" a6="$5"
  local b2=$(( a1*a1 + 4*a2 ))
  local b4=$(( 2*a4 + a1*a3 ))
  local b6=$(( a3*a3 + 4*a6 ))
  local b8=$(( a1*a1*a6 + 4*a2*a6 - a1*a3*a4 + a2*a3*a3 - a4*a4 ))
  local delta=$(( -1*b2*b2*b8 - 8*b4*b4*b4 - 27*b6*b6 + 9*b2*b4*b6 ))
  printf "%s\t%s\t%s\t%s\t%s\n" "$b2" "$b4" "$b6" "$b8" "$delta"
}

modp(){ local x="$1" p="$2"; x=$(( x % p )); [ "$x" -lt 0 ] && x=$((x+p)); printf "%d" "$x"; }

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

legendre(){
  local a=$(modp "$1" "$2") p="$2"
  [ "$a" -eq 0 ] && { echo 0; return; }
  local e=$(( (p-1)/2 ))
  local t=$(powmod "$a" "$e" "$p")
  case "$t" in 1) echo 1;; 0) echo 0;; *) echo -1;; esac
}

vp(){
  local n="$1" p="$2" v=0 s
  [ "$n" -lt 0 ] && n=$(( -n ))
  [ "$n" -eq 0 ] && { echo 99; return; }
  while :; do s=$(( n % p )); [ "$s" -ne 0 ] && break; v=$((v+1)); n=$(( n / p )); done
  echo "$v"
}

is_prime(){ local n="$1" i; [ "$n" -lt 2 ] && return 1; for ((i=2;i*i<=n;i++)); do ((n%i))||return 1; done; return 0; }

# Count points for y^2 + a1xy + a3y = x^3 + a2x^2 + a4x + a6 over F_p (p odd)
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
    sum=$(( sum + 1 + chi ))
  done
  printf "%d" $(( sum + 1 ))
}

reduction_class(){
  local p="$1" b2="$2" b4="$3" b6="$4" b8="$5" delta="$6"
  local vd=$(vp "$delta" "$p")
  if [ "$vd" -eq 0 ]; then echo good; return; fi
  if [ "$vd" -eq 1 ]; then echo mult; return; fi
  echo add
}

local_root_number_mul_pge5(){
  local p="$1" c6="$2" cls="$3"
  [ "$p" -lt 5 ] && { echo unknown; return; }
  [ "$cls" != "mult" ] && { echo unknown; return; }
  local sq=$(legendre "$c6" "$p")
  [ "$sq" -eq 1 ]  && { echo "-1"; return; }  # split
  [ "$sq" -eq -1 ] && { echo "+1"; return; }  # non-split
  echo unknown
}

aggregate_root_number(){
  local list="$1" w=-1  # w_∞ = -1 for E/Q
  while read -r p wp; do
    [ -z "$p" ] && continue
    [ "$wp" = "+1" ] && : || [ "$wp" = "-1" ] && w=$((w*-1))
  done <<< "$list"
  echo "$w"
}
