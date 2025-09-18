set -Eeuo pipefail

# powmod (fast exp) and Legendre symbol (p odd)
powmod(){ local a="$1" e="$2" p="$3" r=1; a=$((a%p)); [ "$a" -lt 0 ] && a=$((a+p))
  while [ "$e" -gt 0 ]; do
    if [ $((e&1)) -eq 1 ]; then r=$(( (r*a)%p )); fi
    a=$(( (a*a)%p )); e=$((e>>1))
  done; printf "%d\n" "$r"; }

legendre(){ # returns 1, p-1 (≡-1 mod p), or 0
  local a="$1" p="$2"; [ $((a%p)) -eq 0 ] && { echo 0; return; }
  powmod "$a" $(( (p-1)/2 )) "$p"
}

# Compute b-invariants and c4,c6,Δ (small coef regime; 64-bit OK here)
tau_invariants() { # a1 a2 a3 a4 a6  ->  c4 c6 Δ
  local a1="$1" a2="$2" a3="$3" a4="$4" a6="$5"
  local b2=$(( a1*a1 + 4*a2 ))
  local b4=$(( a1*a3 + 2*a4 ))
  local b6=$(( a3*a3 + 4*a6 ))
  local b8=$(( a1*a1*a6 + 4*a2*a6 - a1*a3*a4 + a2*a3*a3 - a4*a4 ))
  # standard formulas
  local c4=$(( b2*b2 - 24*b4 ))
  local c6=$(( -b2*b2*b2 + 36*b2*b4 - 216*b6 ))
  local delta=$(( -1*b2*b2*b8 - 8*b4*b4*b4 - 27*b6*b6 + 9*b2*b4*b6 ))
  printf "%d\t%d\t%d\n" "$c4" "$c6" "$delta"
}

vp(){ # v_p(n) for n!=0 (trial division; small conductors)
  local n="$1" p="$2" v=0; [ "$n" -lt 0 ] && n=$((-n))
  [ "$n" -eq 0 ] && { echo 99; return; }
  while [ $((n%p)) -eq 0 ]; do n=$((n/p)); v=$((v+1)); done
  echo "$v"
}

# Local root sign at p≥5; returns "+1" | "-1" | "?"
local_root_sign(){
  local p="$1" c4="$2" c6="$3" delta="$4"
  [ "$p" -lt 5 ] && { echo "?"; return; }
  local vD vC4; vD=$(vp "$delta" "$p"); vC4=$(vp "$c4" "$p")
  if [ "$vD" -eq 0 ]; then echo "+1"; return; fi            # good
  if [ "$vC4" -eq 0 ]; then                                # multiplicative
    # split iff -c6 is a square mod p
    local m=$(( (-c6)%p )); [ "$m" -lt 0 ] && m=$((m+p))
    local ls; ls=$(legendre "$m" "$p")
    if [ "$ls" -eq 1 ]; then echo "-1"; else echo "+1"; fi # split:-1, non-split:+1
    return
  fi
  echo "?"                                                # additive (we refuse to guess)
}

# Global root number: returns JSON: {"global":"±1|unknown","locals":{"p":"±1|?"...}}
compute_root_number_json(){
  local conductor="$1" a1="$2" a2="$3" a3="$4" a4="$5" a6="$6"
  local c4 c6 delta; IFS=$'\t' read -r c4 c6 delta < <(tau_invariants "$a1" "$a2" "$a3" "$a4" "$a6")
  # factor N
  local n primes=() p=2
  n="$conductor"
  while [ $((n%2)) -eq 0 ]; do primes+=("2"); n=$((n/2)); done
  p=3; while [ $((p*p)) -le "$n" ]; do
    while [ $((n%p)) -eq 0 ]; do primes+=("$p"); n=$((n/p)); done
    p=$((p+2))
  done
  [ "$n" -gt 1 ] && primes+=("$n")
  # unique primes
  local uniq=() last=""; IFS=$'\n' read -r -d '' -a uniq < <(printf "%s\n" "${primes[@]}" | sort -n | uniq && printf '\0')
  # locals
  local any_unknown=0 locals_json="{" first=1
  for q in "${uniq[@]}"; do
    local s; s=$(local_root_sign "$q" "$c4" "$c6" "$delta")
    [ "$first" -eq 1 ] || locals_json+=","
    locals_json+="\"$q\":\"$s\""; first=0
    [ "$s" = "?" ] && any_unknown=1
  done
  locals_json+="}"
  # global = w_infty * ∏ known locals; w_infty = -1 for weight 2
  local prod=-1
  if [ "${#uniq[@]}" -gt 0 ]; then
    for q in "${uniq[@]}"; do
      # pull s again (cheap)
      local s; s=$(local_root_sign "$q" "$c4" "$c6" "$delta")
      if [ "$s" = "+1" ]; then :
      elif [ "$s" = "-1" ]; then prod=$(( -prod ))
      else any_unknown=1
      fi
    done
  fi
  if [ "$any_unknown" -eq 1 ]; then
    printf '{"global":"unknown","locals":%s}\n' "$locals_json"
  else
    local g="+1"; [ "$prod" -lt 0 ] && g="-1"
    printf '{"global":"%s","locals":%s}\n' "$g" "$locals_json"
  fi
}

# Smoothed Euler product from a_p panel (TSV: p <tab> a_p), with cutoff X damping.
# Two-scale check: X and 1.2X at s=1/2 and s=1
dual_scale_numerics_json(){
  local panel="$1"
  [ -s "$panel" ] || { printf '{"stable":false,"reason":"no_panel"}\n'; return; }
  local pmax; pmax=$(awk 'NR>1{p=$1+0} END{print (p?p:0)}' "$panel")
  [ "$pmax" -eq 0 ] && { printf '{"stable":false,"reason":"empty_panel"}\n'; return; }
  # compute product at s with damping exp(-p/X)
  awk -v Xbase="sqrt("$(printf '%.12f\n' "$pmax")")" -v panel="$panel" '
    function prod_at_s(s, X,   p,ap,w,fac,prod,line){
      prod=1.0
      while ((getline line < panel)>0){
        if (line ~ /^[[:space:]]*#/ || line ~ /^[[:space:]]*$/) continue
        split(line, t, "\t"); p=t[1]+0; ap=t[2]+0
        w = exp(-p/X)                              # smooth cutoff
        fac = 1.0 / (1.0 - w*ap/pow(p,s) + w*w*pow(p,1.0-2.0*s))
        prod *= fac
      }
      close(panel); return prod
    }
    function round12(x,   s){ s = sprintf("%.12f", x); return s }
    BEGIN{
      X1 = Xbase; X2 = 1.2*Xbase
      Lh1 = prod_at_s(0.5, X1); Lh2 = prod_at_s(0.5, X2)
      L11 = prod_at_s(1.0, X1); L12 = prod_at_s(1.0, X2)
      rLh1 = round12(Lh1); rLh2 = round12(Lh2)
      rL11 = round12(L11); rL12 = round12(L12)
      stable = (rLh1==rLh2 && rL11==rL12) ? "true" : "false"
      printf("{\"stable\":%s,\"L_half\":\"%s\",\"L_half_alt\":\"%s\",\"L1\":\"%s\",\"L1_alt\":\"%s\",\"X\":\"%.6f\",\"X_alt\":\"%.6f\"}\n",
             stable, rLh1, rLh2, rL11, rL12, X1, X2)
    }' </dev/null
}
