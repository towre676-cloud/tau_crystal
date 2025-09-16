#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
cd "$(dirname "$0")/../.." || exit 1

OUT_HITS="analysis/discovery_hits.tsv"
OUT_BEST="analysis/discovery_best.tsv"

# --- 0) Phase angle φ from Laurent (fallback 0)
phi="0"
if [ -s analysis/laurent_ring.tsv ]; then
  # last row: re im Kk q seed
  phi="$(awk 'END{re=$1+0;im=$2+0; if(re!=re||im!=im){re=1;im=0}; print atan2(im,re)}' analysis/laurent_ring.tsv 2>/dev/null || echo 0)"
fi

# --- 1) Seed: prefer Heegner override, else passport/fused JSON
nonce="${PHYSICS_SEED_OVERRIDE:-}"
if [ -z "$nonce" ]; then
  nonce="$(awk -v key=nonce_hex -v def="" -f scripts/tools/read_kv2.awk analysis/passport_sig.tsv 2>/dev/null || true)"
fi
if [ -z "$nonce" ] && [ -s analysis/fused_gates.json ]; then
  nonce="$(grep -o "\"nonce\":\"[0-9a-fA-F]\{16,64\}\"" -m1 analysis/fused_gates.json | sed 's/.*"nonce":"//; s/".*//' || true)"
fi
[ -z "$nonce" ] && { echo "[discovery] no nonce found"; exit 1; }

# 32 hex chars gives us two 32-bit ints; pad if shorter
nonce="$(echo "$nonce" | tr -dc '0-9a-fA-F')"
nonce="${nonce}00000000000000000000000000000000"

h1=${nonce:0:8}; h2=${nonce:8:8}; h3=${nonce:16:8}; h4=${nonce:24:8}
u1=$((16#$h1)); u2=$((16#$h2)); u3=$((16#$h3)); u4=$((16#$h4))

# --- 2) Prime panel, deltas, scales via env (defaults handled by analytic gate)
panel_str="${RANK_PANEL:-2 3 5 7 11 13 17 19 23 29 31 37 41 43 47 53 59 61 67 71 73 79 83 89 97}"
set -- $panel_str; PRIMES=("$@"); tested=${#PRIMES[@]}

# --- 3) Base N,k from seed
# odd baseline N from u1; k in [2..129]
N=$(( (u1 | 1) ))
k=$(( (u2 & 127) + 2 ))

# --- 4) Optional auto-direction from past histograms (bias by best decade)
if [ -z "${FORCE_DECADE:-}" ] && [ -s analysis/hist_discovery_Nk.tsv ]; then
  best_decade="$(awk -F'\t' 'NR>1 { if($3+0>max){max=$3+0; best=$1} } END{ if(best!="") print int(best) }' analysis/hist_discovery_Nk.tsv 2>/dev/null || true)"
  if [ -n "$best_decade" ]; then
    d="$best_decade"
    case "$d" in (*[!0-9]*|'') d=0;; esac
    [ "$d" -lt 0 ] && d=0
    MAX_DECADE="${MAX_DECADE:-9}"
    [ "$d" -gt "$MAX_DECADE" ] && d="$MAX_DECADE"
    base=1; i=0
    while [ "$i" -lt "$d" ]; do base=$((base*10)); i=$((i+1)); done
    jitter=$(( (u1 % 9) + 1 ))   # 1..9
    N=$(( base * jitter ))
    echo "[discovery] biasing N toward decade 10^$d → N≈$N (cap=$MAX_DECADE)"
  fi
fi

# --- 5) Ramanujan surrogate: mean/min of |cos(p φ)| / sqrt(p)
mean_num=0
min_r=-1
for p in "${PRIMES[@]}"; do
  r="$(awk -v p="$p" -v phi="$phi" 'BEGIN{print (cos(p*phi)/exp(0.5*log(p))); }')"
  # absolute value
  r_abs="$(awk -v x="$r" 'BEGIN{print (x<0?-x:x)}')"
  mean_num="$(awk -v a="$mean_num" -v b="$r_abs" 'BEGIN{print a+b}')"
  if [ "$min_r" = "-1" ]; then min_r="$r_abs"; else
    min_r="$(awk -v m="$min_r" -v v="$r_abs" 'BEGIN{print (v<m?v:m)}')"
  fi
done
mean_r="$(awk -v s="$mean_num" -v n="$tested" 'BEGIN{if(n<1)n=1; print s/n}')"

# --- 6) Emit/compare; improvement = smaller mean_r
[ -f "$OUT_HITS" ] || printf "mean_r\tmin_r\tN\tk\ttested\tprimes\tphi\tnonce\n" > "$OUT_HITS"
printf "%.6f\t%.6f\t%d\t%d\t%d\t%s\t%.6f\t%s\n" \
  "$mean_r" "$min_r" "$N" "$k" "$tested" "$panel_str" "$phi" "$nonce" >> "$OUT_HITS"

if [ -s "$OUT_BEST" ]; then
  best="$(awk 'NR==1{print $1}' "$OUT_BEST" 2>/dev/null || echo)"
else
  best=""
fi

if [ -z "$best" ] || awk -v m="$mean_r" -v b="$best" 'BEGIN{exit !(m<b)}'; then
  printf "%.6f\t%d\t%d\t%d\t%.6f\t%s\n" "$mean_r" "$N" "$k" "$tested" "$phi" "$nonce" > "$OUT_BEST"
  echo "[discovery] new record: mean_r=$mean_r N=$N k=$k tested=$tested"
  exit 0
else
  echo "[discovery] no improvement (mean_r=$mean_r best=$best)"
  exit 1
fi
