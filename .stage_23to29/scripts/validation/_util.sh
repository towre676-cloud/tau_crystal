powmod(){ local a=$1 b=$2 m=$3 r=1; a=$((a%m)); while [ $b -gt 0 ]; do if [ $((b&1)) -eq 1 ]; then r=$(( (r*a)%m )); fi; a=$(( (a*a)%m )); b=$((b>>1)); done; echo $r; }
legendre(){ local a=$1 p=$2; a=$(( (a%p+p)%p )); [ $a -eq 0 ] && { echo 0; return; }; local e=$(( (p-1)/2 )); local t=$(powmod $a $e $p); [ $t -eq 1 ] && echo 1 || echo -1; }
gcd(){ local a=$1 b=$2 t; [ $a -lt 0 ] && a=$((-a)); [ $b -lt 0 ] && b=$((-b)); while [ $b -ne 0 ]; do t=$((a%b)); a=$b; b=$t; done; echo $a; }
egcd(){ local a=$1 b=$2 x0=1 y0=0 x1=0 y1=1 q t; while [ $b -ne 0 ]; do q=$((a/b)); t=$((a-q*b)); a=$b; b=$t; t=$((x0-q*x1)); x0=$x1; x1=$t; t=$((y0-q*y1)); y0=$y1; y1=$t; done; echo "$x0 $y0 $a"; }
invmod(){ local a=$1 m=$2; read x y g < <(egcd $a $m); [ $g -ne 1 ] && { echo -1; return; }; local r=$((x%m)); [ $r -lt 0 ] && r=$((r+m)); echo $r; }
hash_to_z(){ local S="$1" M="$2"; local H; H=$(printf "%s" "$S" | sha256sum | awk '{print $1}'); printf "%d" "$(( 0x${H:0:15} % M ))"; }
