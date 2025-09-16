#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
cd "$(dirname "$0")/../.." || exit 1

OUT_HITS="analysis/discovery_hits.tsv"
OUT_BEST="analysis/discovery_best.tsv"

# --- φ from Laurent (fallback 0) --------------------------------------------
phi="0"
if [ -s analysis/laurent_ring.tsv ]; then
  phi="$(awk 'END{re=$1+0;im=$2+0; if(re!=re||im!=im){re=1;im=0}; print atan2(im,re)}' analysis/laurent_ring.tsv 2>/dev/null || echo 0)"
fi

# --- seed: Heegner override → passport → fused JSON -------------------------
nonce="${PHYSICS_SEED_OVERRIDE:-}"
if [ -z "$nonce" ] && [ -s analysis/passport_sig.tsv ]; then
  nonce="$(awk -v key=nonce_hex -v def="" -f scripts/tools/read_kv2.awk analysis/passport_sig.tsv 2>/dev/null || true)"
fi
if [ -z "$nonce" ] && [ -s analysis/fused_gates.json ]; then
  nonce="$(grep -o "\"nonce\":\"[0-9a-fA-F]\{16,64\}\"" -m1 analysis/fused_gates.json | sed 's/.*"nonce":"//; s/".*//' || true)"
fi
[ -z "$nonce" ] && { echo "[discovery] no nonce found"; exit 1; }
nonce="$(echo "$nonce" | tr -dc '0-9a-fA-F')"; nonce="${nonce}00000000000000000000000000000000"

h1=${nonce:0:8}; h2=${nonce:8:8}; h3=${nonce:16:8}; h4=${nonce:24:8}
u1=$((16#$h1)); u2=$((16#$h2)); u3=$((16#$h3)); u4=$((16#$h4))

# --- panel/deltas via env (defaults = 25 primes) ----------------------------
panel_str="${RANK_PANEL:-2 3 5 7 11 13 17 19 23 29 31 37 41 43 47 53 59 61 67 71 73 79 83 89 97}"
set -- $panel_str; PRIMES=("$@"); tested=${#PRIMES[@]}

# --- base N,k from seed ------------------------------------------------------
N=$(( (u1 | 1) ))               # odd baseline
k=$(( (u2 & 127) + 2 ))         # 2..129

# --- weighted top-3 decade bias (no arrays, no **) --------------------------
if [ -z "${FORCE_DECADE:-}" ] && [ -s analysis/hist_discovery_Nk.tsv ]; then
  D="$(
    awk -F'\t' -v u4="$u4" '
      NR>1{
        if(NF>=3) c[$1]+=$3+0;
        else if(NF>=2) c[$1]+=$2+0;
        else c[$1]++
      }
      END{
        t1c=t2c=t3c=0; t1d=t2d=t3d=0;
        for(d in c){
          cc=c[d]+0
          if(cc>t1c){t3c=t2c; t3d=t2d; t2c=t1c; t2d=t1d; t1c=cc; t1d=d}
          else if(cc>t2c){t3c=t2c; t3d=t2d; t2c=cc; t2d=d}
          else if(cc>t3c){t3c=cc; t3d=d}
        }
        W=t1c+t2c+t3c
        if(W<=0){exit}
        pick=u4%W
        if(pick<t1c)      print t1d
        else if(pick<t1c+t2c) print t2d
        else               print t3d
      }' analysis/hist_discovery_Nk.tsv 2>/dev/null || true
  )"
  if [ -n "$D" ]; then
    case "$D" in (*[!0-9]*|'') D=0;; esac
    [ "$D" -lt 0 ] && D=0
    MAX_DECADE="${MAX_DECADE:-9}"
    [ "$D" -gt "$MAX_DECADE" ] && D="$MAX_DECADE"
    base=1; i=0
    while [ "$i" -lt "$D" ]; do base=$((base*10)); i=$((i+1)); done
    jitter=$(( (u1 % 9) + 1 ))    # 1..9
    N=$(( base * jitter ))
    echo "[discovery] weighted decade: 10^$D (cap=$MAX_DECADE) → N≈$N"
  fi
fi

# --- de-dup (N,k) within hits; if seen, nudge jitter in same decade ---------
if [ -s analysis/discovery_hits.tsv ]; then
  if awk -F'\t' -v N="$N" -v k="$k" 'NR>1 && $3==N && $4==k {found=1} END{exit !found}' analysis/discovery_hits.tsv
  then
    # recompute base from N’s decade and move to a new 1..9 bucket
    Dlocal=0; tmp=$N; while [ $tmp -ge 10 ]; do tmp=$((tmp/10)); Dlocal=$((Dlocal+1)); done
    base=1; i=0; while [ "$i" -lt "$Dlocal" ]; do base=$((base*10)); i=$((i+1)); done
    jitter=$(( ((u3 % 9) + 1) ))
    N=$(( base * jitter ))
    echo "[discovery] (N,k) seen; nudged N→$N"
  fi
fi

# --- Ramanujan surrogate: mean/min of |cos(p φ)|/sqrt(p) --------------------
mean_num=0; min_r=-1
for p in "${PRIMES[@]}"; do
  r="$(awk -v p="$p" -v phi="$phi" 'BEGIN{print (cos(p*phi)/exp(0.5*log(p))); }')"
  r_abs="$(awk -v x="$r" 'BEGIN{print (x<0?-x:x)}')"
  mean_num="$(awk -v a="$mean_num" -v b="$r_abs" 'BEGIN{print a+b}')"
  if [ "$min_r" = "-1" ]; then min_r="$r_abs"; else
    min_r="$(awk -v m="$min_r" -v v="$r_abs" 'BEGIN{print (v<m?v:m)}')"
  fi
done
mean_r="$(awk -v s="$mean_num" -v n="$tested" 'BEGIN{if(n<1)n=1; print s/n}')"

# --- emit & record best ------------------------------------------------------
[ -f "$OUT_HITS" ] || printf "mean_r\tmin_r\tN\tk\ttested\tprimes\tphi\tnonce\n" > "$OUT_HITS"
printf "%.6f\t%.6f\t%d\t%d\t%d\t%s\t%.6f\t%s\n" "$mean_r" "$min_r" "$N" "$k" "$tested" "$panel_str" "$phi" "$nonce" >> "$OUT_HITS"

best=""
[ -s "$OUT_BEST" ] && best="$(awk 'NR==1{print $1}' "$OUT_BEST" 2>/dev/null || echo)"
if [ -z "$best" ] || awk -v m="$mean_r" -v b="$best" 'BEGIN{exit !(m<b)}'; then
  printf "%.6f\t%d\t%d\t%d\t%.6f\t%s\n" "$mean_r" "$N" "$k" "$tested" "$phi" "$nonce" > "$OUT_BEST"
  echo "[discovery] new record: mean_r=$mean_r N=$N k=$k tested=$tested"
  exit 0
else
  echo "[discovery] no improvement (mean_r=$mean_r best=$best)"
  exit 1
fi
