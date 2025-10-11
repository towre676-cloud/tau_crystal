#!/usr/bin/env sh
# Usage: ./lrc_structured_sweep.sh OUT.csv Nmin Nmax kmin kmax S_ap S_copr S_clust
set -e
OUT="${1:-lrc_structured.csv}"
NMIN="${2:-5}"; NMAX="${3:-12}"
KMIN="${4:-2}"; KMAX="${5:-8}"
SAP="${6:-3}"; SCOPR="${7:-3}"; SCLUST="${8:-3}"

echo "N,k,family,a_list,cont_s_num,cont_s_den,cont_max_num,cont_max_den,cont_OK,disc_s_num,disc_s_den,disc_max_num,disc_max_den,disc_OK,s_den_divides_N,agree_max,why_miss,thr_num,thr_den,slack_num,slack_den,beats_bound" > "$OUT"

gcd(){ a=$1; b=$2; [ "$a" -lt 0 ] && a=$(( -a )); [ "$b" -lt 0 ] && b=$(( -b )); while [ "$b" -ne 0 ]; do t=$((a % b)); a=$b; b=$t; done; echo "$a"; }
reduce(){ n=$1; d=$2; g=$(gcd "$n" "$d"); [ "$g" -eq 0 ] && { echo "0,1"; return; }; echo "$((n/g)),$((d/g))"; }

pick_coprime_set() {
  N="$1"; K="$2"
  seq 1 $((N-1)) | awk -v N="$N" '
    function gcd(a,b){while(b){t=a%b;a=b;b=t}return a}
    { if (gcd($1,N)==1) print $1 }' \
  | awk 'BEGIN{srand()} {print rand(),$0}' | sort -k1,1n \
  | awk '{print $2}' | head -n "$K" | xargs
}

pick_cluster_set() {
  N="$1"; K="$2"
  W=$(( (N+9)/10 )); [ "$W" -lt 2 ] && W=2
  C=$(awk -v N="$N" 'BEGIN{srand(); print 1+int(rand()*(N-1))}')
  A=$(seq 1 $((N-1)) | awk -v c="$C" -v W="$W" '{if($1>=c-W && $1<=c+W) print $1}' \
       | awk 'BEGIN{srand()} {print rand(),$0}' | sort -k1,1n \
       | awk '{print $2}' | head -n "$K" | xargs)
  got=$(printf "%s\n" $A | wc -w | tr -d ' ')
  if [ "$got" -lt "$K" ]; then
    EXTRA=$(comm -23 <(seq 1 $((N-1)) | sort) <(printf "%s\n" $A | sort) \
       | awk 'BEGIN{srand()} {print rand(),$0}' | sort -k1,1n \
       | awk '{print $2}' | head -n $((K-got)) | xargs)
    A="$A $EXTRA"; A=$(echo "$A" | xargs)
  fi
  echo "$A"
}

emit_row() {
  N="$1"; K="$2"; FAMILY="$3"; A="$4"
  row=$(./lrc_csv_both.sh "$N" $A)
  IFS=, read -r cN ck calist c_sN c_sD c_mN c_mD c_OK d_sN d_sD d_mN d_mD d_OK div_ok agree why_miss <<EOF
$row
EOF
  thrN=1; thrD=$((K+1))
  num=$(( d_mN*(K+1) - d_mD ))
  den=$(( d_mD*(K+1) ))
  IFS=, read sN sD <<EOF
$(reduce "$num" "$den")
EOF
  beats="NO"; [ "$num" -gt 0 ] && beats="YES"
  echo "$N,$K,$FAMILY,\"$A\",$c_sN,$c_sD,$c_mN,$c_mD,$c_OK,$d_sN,$d_sD,$d_mN,$d_mD,$d_OK,$div_ok,$agree,$why_miss,$thrN,$thrD,$sN,$sD,$beats" >> "$OUT"
}

for N in $(seq "$NMIN" "$NMAX"); do
  for K in $(seq "$KMIN" "$KMAX"); do
    [ "$K" -ge "$N" ] && continue

    # AP samples (avoid duplicate start when the two starts coincide)
    max_step=$(( (N-1)/(K-1) ))
    if [ "$max_step" -ge 1 ]; then
      steps=$(seq 1 "$max_step" | awk 'BEGIN{srand()} {print rand(),$0}' | sort -k1,1n | awk '{print $2}' | head -n "$SAP")
      for s in $steps; do
        start1=1
        start2=$(( 1 + ( (N-1 - (K-1)*s) / 2 ) ))
        last=""
        for start in "$start1" "$start2"; do
          [ "$start" = "$last" ] && continue
          last="$start"
          end=$(( start + (K-1)*s ))
          [ "$start" -lt 1 ] && continue
          [ "$end" -gt $((N-1)) ] && continue
          A=""
          for m in $(seq 0 $((K-1))); do A="$A $((start + m*s))"; done
          A=$(echo "$A" | xargs)
          emit_row "$N" "$K" "AP" "$A"
        done
      done
    fi

    # COPRIME samples
    for _ in $(seq 1 "$SCOPR"); do
      A=$(pick_coprime_set "$N" "$K")
      [ -n "$A" ] && emit_row "$N" "$K" "COPRIME" "$A"
    done

    # CLUSTER samples
    for _ in $(seq 1 "$SCLUST"); do
      A=$(pick_cluster_set "$N" "$K")
      emit_row "$N" "$K" "CLUSTER" "$A"
    done
  done
done
