#!/usr/bin/env sh
# Usage:
#   ./lrc_structured_resweep_multiples.sh OUT Nmin Nmax Kmin Kmax CNT_AP CNT_COP CNT_CL [denoms_by_k.txt]
set -u

OUT="${1:?out.csv}"; shift || true
NMIN="${1:-5}"; NMAX="${2:-60}"; KMIN="${3:-2}"; KMAX="${4:-10}"
CNT_AP="${5:-3}"; CNT_COP="${6:-3}"; CNT_CL="${7:-3}"
DENF="${8:-denoms_by_k.txt}"

[ -x ./lrc_csv_both.sh ] || { echo "need ./lrc_csv_both.sh" >&2; exit 1; }

# header
printf '%s\n' "N,k,family,a_list,cont_s_num,cont_s_den,cont_max_num,cont_max_den,cont_OK,disc_s_num,disc_s_den,disc_max_num,disc_max_den,disc_OK,s_den_divides_N,agree_max,why_miss,thr_num,thr_den,slack_num,slack_den,beats_bound" > "$OUT"

# ---- helpers ---------------------------------------------------------------
gcd(){ a=$1; b=$2; while [ "$b" -ne 0 ]; do t=$((a%b)); a=$b; b=$t; done; echo "$a"; }
rint(){ a=$1; b=$2; echo $(( a + (RANDOM % (b - a + 1)) )); }

keep_pair(){ # keep (N,k) if any learned denom | or N%(k+1)=0
  k=$1 N=$2
  if [ -f "$DENF" ] && awk -F, -v k="$k" -v N="$N" '$1==k && $2>0 { if (N%$2==0){ok=1; exit} } END{exit (ok?0:1)}' "$DENF"
  then [ "${LRC_DEBUG:-}" ] && echo "[keep] k=$k N=$N hits learned denom" >&2; return 0; fi
  if [ $(( N % (k+1) )) -eq 0 ]; then
    [ "${LRC_DEBUG:-}" ] && echo "[keep] k=$k N=$N hits fallback (k+1)" >&2; return 0
  fi
  [ "${LRC_DEBUG:-}" ] && echo "[skip] k=$k N=$N (no denom divides)" >&2
  return 1
}

emit_row(){ # N K FAM "a1 ... aK"
  N=$1; K=$2; FAM=$3; ALIST="$4"
  [ -z "$ALIST" ] && { [ "${LRC_DEBUG:-}" ] && echo "[gen-fail] $FAM N=$N K=$K" >&2; return 0; }
  RAW=$(./lrc_csv_both.sh "$N" $ALIST) || return 0
  TAIL=$(printf '%s\n' "$RAW" | awk -F, '{out=""; for(i=4;i<=NF;i++) out=(out?out","$i:$i); print out}')
  printf '%s\n' "$N,$K,$FAM,\"$ALIST\",$TAIL" >> "$OUT"
}

# ---- robust generators ------------------------------------------------------
gen_ap(){ # AP mod N with gcd(d,N)=1, no 0 in the first K terms, all distinct
  N=$1 K=$2
  tries=0
  while [ $tries -lt 100 ]; do
    r=$(rint 1 $((N-1)))
    d=$(rint 1 $((N-1)))
    [ "$(gcd "$d" "$N")" -ne 1 ] && { tries=$((tries+1)); continue; }
    ok=1; out=""
    j=0
    while [ $j -lt $K ]; do
      x=$(( (r + j*d) % N ))
      [ $x -eq 0 ] && { ok=0; break; }
      # distinct guaranteed by gcd(d,N)=1 across j, but be defensive:
      for y in $out; do [ "$y" -eq "$x" ] && { ok=0; break; }; done
      [ $ok -eq 0 ] && break
      out="$out $x"; j=$((j+1))
    done
    [ $ok -eq 1 ] && { echo "$out" | awk '{$1=$1;print}'; return; }
    tries=$((tries+1))
  done
  echo ""
}

gen_coprime(){ # pick K distinct a in 1..N-1 with gcd(a,N)=1 (shuffle via awk)
  N=$1 K=$2
  awk -v N="$N" 'BEGIN{for(i=1;i<N;i++) if (gcd(i,N)==1) printf "%d\n", i}
    function gcd(a,b){while(b){t=a%b;a=b;b=t}return a}' \
  | awk 'BEGIN{srand()} {print rand(),$0}' | sort -k1,1n | awk '{print $2}' \
  | head -n "$K" | xargs | awk '{$1=$1;print}'
}

gen_cluster(){ # cluster of width ~K+1 around random pivot (distinct, in-range)
  N=$1 K=$2
  p=$(rint 2 $((N-2))); w=$((K+1))
  lo=$((p - w/2)); [ $lo -lt 1 ] && lo=1
  hi=$((lo + w - 1)); [ $hi -gt $((N-1)) ] && { hi=$((N-1)); lo=$((hi-w+1)); [ $lo -lt 1 ] && lo=1; }
  out=""; tries=0
  while [ "$(set -- $out; echo $#)" -lt $K ] && [ $tries -lt 200 ]; do
    x=$(rint "$lo" "$hi")
    dup=0; for y in $out; do [ "$y" -eq "$x" ] && { dup=1; break; }; done
    [ $dup -eq 0 ] && out="$out $x"
    tries=$((tries+1))
  done
  echo "$out" | awk '{$1=$1;print}'
}

# ---- main -------------------------------------------------------------------
for N in $(seq "$NMIN" "$NMAX"); do
  for K in $(seq "$KMIN" "$KMAX"); do
    [ "$K" -lt "$N" ] || continue
    keep_pair "$K" "$N" || continue

    i=1; while [ $i -le "$CNT_AP"  ]; do emit_row "$N" "$K" "AP"      "$(gen_ap      "$N" "$K")"; i=$((i+1)); done
    i=1; while [ $i -le "$CNT_COP" ]; do emit_row "$N" "$K" "COPRIME" "$(gen_coprime "$N" "$K")"; i=$((i+1)); done
    i=1; while [ $i -le "$CNT_CL"  ]; do emit_row "$N" "$K" "CLUSTER" "$(gen_cluster "$N" "$K")"; i=$((i+1)); done
  done
done
