#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
cd "$(dirname "$0")/../.." || exit 1

OUT_HITS="analysis/discovery_hits.tsv"
OUT_BEST="analysis/discovery_best.tsv"

# --- Laurent phase φ (fallback 0) -------------------------------------------
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

# --- prime panel (25 defaults) ----------------------------------------------
panel_str="${RANK_PANEL:-2 3 5 7 11 13 17 19 23 29 31 37 41 43 47 53 59 61 67 71 73 79 83 89 97}"
set -- $panel_str; PRIMES=("$@"); tested=${#PRIMES[@]}

# --- baseline N,k ------------------------------------------------------------
N=$(( (u1 | 1) ))               # odd baseline
k=$(( (u2 & 127) + 2 ))         # 2..129

# --- helpers ----------------------------------------------------------------
pow10() { # 10^d without ** (portable)
  d="$1"; b=1; i=0; while [ "$i" -lt "$d" ]; do b=$((b*10)); i=$((i+1)); done; echo "$b";
}
clamp_k() { kk="$1"; [ "$kk" -lt 2 ] && kk=2; [ "$kk" -gt 129 ] && kk=129; echo "$kk"; }

# --- strategy: choose one of 3 modes (weighted by seed) ---------------------
mode=$(( u4 % 3 ))
MAX_DECADE="${MAX_DECADE:-9}"

best_N=""; best_k=""
if [ -s "$OUT_BEST" ]; then
  read best_mean best_N best_k _rest < "$OUT_BEST" 2>/dev/null || true
fi

if [ "$mode" -eq 0 ]; then
  # (A) Target successful decade ±1 around best, else sweet-spot 10^5..10^6
  if [ -n "$best_N" ]; then
    base_decade="$(awk -v N="$best_N" 'BEGIN{if(N<=0){print 5; exit} print int(log(N)/log(10))}')"
    shift_dec=$(( (u1 % 3) - 1 ))                  # -1,0,+1
    target_dec=$(( base_decade + shift_dec ))
    [ "$target_dec" -lt 0 ] && target_dec=0
    [ "$target_dec" -gt "$MAX_DECADE" ] && target_dec="$MAX_DECADE"
    base="$(pow10 "$target_dec")"
    jitter=$(( (u1 % 9) + 1 ))                     # 1..9
    N=$(( base * jitter ))
    # keep k near best if we have one
    if [ -n "$best_k" ]; then
      k_off=$(( (u2 % 11) - 5 ))                   # ±5
      k="$(clamp_k $(( best_k + 2*k_off )))"
    fi
    echo "[discovery] targeted decade: 10^$target_dec (cap=$MAX_DECADE) → N≈$N, k≈$k"
  else
    # default sweet-spot 1e5..1e6
    base="$(pow10 5)"
    N=$(( base * ( (u1 % 10) + 1 ) ))              # 1e5..1e6
    k=$(( 50 + (u2 % 51) ))                        # 50..100
    echo "[discovery] default sweet-spot: N≈$N, k≈$k"
  fi

elif [ "$mode" -eq 1 ]; then
  # (B) Arithmetic family: N = p^3 * q with small primes p∈{2,3,5,7}, q∈{11,13,17,19}
  idx_p=$(( (u1 >> 3) % 4 ))
  case "$idx_p" in 0) p=2;; 1) p=3;; 2) p=5;; *) p=7;; esac
  idx_q=$(( (u1 >> 6) % 4 ))
  case "$idx_q" in 0) q=11;; 1) q=13;; 2) q=17;; *) q=19;; esac
  p3=$(( p*p*p ))
  N=$(( p3 * q ))
  # weight 60–100 to bias to heavier forms
  k=$(( 60 + (u2 % 41) ))                          # 60..100
  echo "[discovery] family p^3*q: p=$p q=$q → N=$N, k=$k"

else
  # (C) Grid around current best (± offsets); fallback to sweet-spot if none
  if [ -n "$best_N" ] && [ -n "$best_k" ]; then
    N_off=$(( (u1 % 21) - 10 ))                    # ±10
    k_off=$(( (u2 % 11) - 5 ))                     # ±5
    N=$(( best_N + 1000 * N_off ))
    k="$(clamp_k $(( best_k + 2*k_off )))"
    [ "$N" -lt 1 ] && N=1
    echo "[discovery] local grid around best: N=$N, k=$k"
  else
    base="$(pow10 5)"; N=$(( base * ( (u1 % 10) + 1 ) )); k=$(( 50 + (u2 % 51) ))
    echo "[discovery] fallback sweet-spot: N≈$N, k≈$k"
  fi
fi

# --- De-dup (N,k) seen → nudge to a new bucket in same decade ---------------
if [ -s "$OUT_HITS" ]; then
  seen="$(awk -F'\t' -v N="$N" -v k="$k" 'NR>1 && $3==N && $4==k {print 1; exit}' "$OUT_HITS" 2>/dev/null)"
  if [ "$seen" = "1" ]; then
    base="$(awk -v n="$N" 'BEGIN{b=1; n=int(n); if(n<0)n=0; while(n>=10){n=int(n/10); b*=10} print b}')"
    jitter=$(( ((u3 % 9) + 1) ))
    N=$(( base * jitter ))
    echo "[discovery] (N,k) seen; nudged N→$N"
  fi
fi

# --- Multi-prime phase coherence gate (0, π/2, π, 3π/2 within 0.1 rad) -----
coh="$(awk -v phi="$phi" 'BEGIN{
  split("2 3 5 7 11",P," "); pi=4*atan2(1,1); thr=0.1; c=0;
  for(i=1;i<=5;i++){ p=P[i]+0; t=p*phi;
    while(t>=2*pi)t-=2*pi; while(t<0)t+=2*pi;
    m=1e9; for(j=0;j<4;j++){g=j*(pi/2); d=t-g; if(d<0)d=-d; if(d<m)m=d}
    if(m<thr)c++
  } print c
}')"
if [ "$coh" -lt 3 ]; then
  echo "[discovery] low coherence (score=$coh) — skip"; exit 1
fi

# --- Ramanujan surrogate: mean/min |cos(pφ)| / sqrt(p) ----------------------
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
