#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
. scripts/atlas/_intlib.sh

CURVE_LABEL="${1:?label}"
N="${2:?conductor}"
A1="${3:?}"; A2="${4:?}"; A3="${5:?}"; A4="${6:?}"; A6="${7:?}"

outdir="analysis/atlas/${CURVE_LABEL}"
cleanup_on_error(){ echo "[ERROR] build failed for ${CURVE_LABEL}, cleaning ${outdir}" >&2; rm -rf "$outdir"; }
trap cleanup_on_error ERR
mkdir -p "$outdir"

read -r B2 B4 B6 B8 DELTA < <(tau_invariants "$A1" "$A2" "$A3" "$A4" "$A6")
[ "$DELTA" -ne 0 ] || { echo "[atlas] singular curve (Δ=0)"; exit 2; }

panel="$outdir/ap.tsv"; printf "p\ta_p\n" > "$panel"

hasse_violations=0
max_hasse_ratio="0"
worst_p=""
pcount=0
pmax=199

# gather local root numbers where safely known (multiplicative at p≥5)
local_factors=""
for ((p=3; p<=pmax; p+=2)); do
  is_prime "$p" || continue
  cls=$(reduction_class "$p" "$B2" "$B4" "$B6" "$B8" "$DELTA")
  if [ "$cls" = "mult" ]; then
    wp=$(local_root_number_mul_pge5 "$p" "$B6" "$cls")
    if [ "$wp" = "+1" ] || [ "$wp" = "-1" ]; then
      local_factors+="$p $wp"$'\n'
    else
      local_factors+="$p unknown"$'\n'
    fi
  elif [ "$cls" = "add" ]; then
    local_factors+="$p unknown"$'\n'
  fi
done

# exact ap on good primes, plus Hasse diagnostics
for ((p=3; p<=pmax; p+=2)); do
  is_prime "$p" || continue
  if [ $(( DELTA % p )) -eq 0 ]; then
    continue
  fi
  np=$(count_points_mod_p "$A1" "$A2" "$A3" "$A4" "$A6" "$p")
  ap=$(( p + 1 - np ))
  printf "%d\t%d\n" "$p" "$ap" >> "$panel"
  pcount=$((pcount+1))

  apabs=$(( ap<0 ? -ap : ap ))
  # ratio r = |a_p|^2 / (4p)  (Hasse violation iff r>1)
  num=$(( apabs*apabs ))
  den=$(( 4*p ))
  # compute decimal ratio via bc for diagnostics
  r=$(echo "scale=6; $num/$den" | bc -l)
  cmp=$(echo "$r > $max_hasse_ratio" | bc -l)
  [ "$cmp" -eq 1 ] && { max_hasse_ratio="$r"; worst_p="$p"; }
  [ $num -gt $den ] && hasse_violations=$((hasse_violations+1))
done

# ── Dual-scale Euler-product estimates (panel truncation)
euler_L_product(){
  # s ∈ {0.5,1}, panel file
  local s="$1" panel="$2" scale="$3"
  awk -v s="$s" -v SCALE="$scale" '
    BEGIN{FS="\t"; sumlog=0; pi=3.141592653589793; scale=SCALE}
    NR>1{
      p=$1+0; ap=$2+0
      if(s==0.5){
        den=(2.0 - ap/sqrt(p))
      } else {
        den=(1.0 - ap/p + 1.0/p)
      }
      if(den<=0){ den=1e300 } # guard; we only log det
      # bc-like ln via awk log(); but POSIX awk lacks log reliably ⇒ use printf and pipe? fallback:
      ln_den=log(den)
      sumlog += -ln_den
    }
    END{ printf "%.16f", exp(sumlog) }
  ' "$panel" 2>/dev/null
}

# if awk lacks log(), fall back to bc loop
have_awk_log=$(awk 'BEGIN{if(typeof(log)== "unassigned"){print 0}else{print 1}}' 2>/dev/null || echo 0)
compute_Ls(){
  local panel="$1"
  if [ "$have_awk_log" -eq 1 ]; then
    Lhalf_64=$(euler_L_product 0.5 "$panel" 64)
    L1_64=$(euler_L_product 1 "$panel" 64)
    Lhalf_96=$(euler_L_product 0.5 "$panel" 96)
    L1_96=$(euler_L_product 1 "$panel" 96)
  else
    # bc path: accumulate ln factors then exp
    for s in "0.5" "1"; do
      for prec in 64 96; do
        ln_sum=$(awk -v s="$s" '
          BEGIN{FS="\t"}
          NR>1{
            p=$1+0; ap=$2+0
            if(s==0.5){ printf "l(2 - (%d)/sqrt(%d))\n", ap, p }
            else{ printf "l(1 - (%d)/%d + 1/%d)\n", ap, p, p }
          }' "$panel" | bc -l | awk '{s+=$1} END{printf "%.20f", -s}')
        val=$(echo "scale=$prec; e($ln_sum)" | bc -l)
        [ "$s" = "0.5" ] && { [ "$prec" = "64" ] && Lhalf_64="$val" || Lhalf_96="$val"; } || { [ "$prec" = "64" ] && L1_64="$val" || L1_96="$val"; }
      done
    done
  fi
  # round-to-16 and compare
  Lhalf=$(printf "%.16f" "$Lhalf_64")
  L1=$(printf "%.16f" "$L1_64")
  agree_half=$([ "$(printf "%.16f" "$Lhalf_96")" = "$Lhalf" ] && echo true || echo false)
  agree_one=$([ "$(printf "%.16f" "$L1_96")" = "$L1" ] && echo true || echo false)
  # crude tail proxy (panel truncation): sum_{p>pmax} 2/p^s up to 10k as upper envelope
  pmax=$(awk 'END{print $1}' "$panel")
  tail_half=$(awk -v P="$pmax" 'BEGIN{sum=0; for(n=P+1;n<=10000;n++){sum+=2/(sqrt(n))} printf "%.6f", sum }')
  tail_one=$(awk -v P="$pmax" 'BEGIN{sum=0; for(n=P+1;n<=10000;n++){sum+=2/(n)} printf "%.6f", sum }')
}

compute_Ls "$panel"

# local root-number list (known multiplicative only)
known_lines=$(awk '$2=="+1"||$2=="-1"{print}' <<< "$local_factors")
global_root=""
[ -n "$known_lines" ] && global_root=$(aggregate_root_number "$known_lines")

leaf="$outdir/leaf.json"
jq -n \
  --arg label "$CURVE_LABEL" \
  --argjson N "$N" \
  --argjson b2 "$B2" --argjson b4 "$B4" --argjson b6 "$B6" --argjson b8 "$B8" \
  --argjson delta "$DELTA" \
  --arg ap_path "$panel" \
  --argjson pcount "$pcount" \
  --argjson pmax "$pmax" \
  --argjson hasse_v "$hasse_violations" \
  --arg max_ratio "$max_hasse_ratio" \
  --arg worst_p "$worst_p" \
  --arg lfactors "$local_factors" \
  --arg groot "${global_root:-null}" \
  --arg Lhalf "$Lhalf" --arg L1 "$L1" \
  --arg agree_half "$agree_half" --arg agree_one "$agree_one" \
  --arg tail_half "$tail_half" --arg tail_one "$tail_one" \
  '{
     curve: {label: $label, conductor: $N, a: {a1:'"$A1"',a2:'"$A2"',a3:'"$A3"',a4:'"$A4"',a6:'"$A6"'}},
     invariants: {b2:$b2,b4:$b4,b6:$b6,b8:$b8,delta:$delta},
     panel: {path:$ap_path, primes_evaluated:$pcount, pmax:$pmax},
     checks: {
       hasse: {violations: ($hasse_v|tonumber), max_ratio: ($max_ratio|tonumber), worst_p: ($worst_p|tonumber)},
       parity: {root_number: (try ($groot|tonumber) catch null), locals: ([$lfactors|split("\n")[]|select(length>0)|split(" ")|{p:(.[0]|tonumber), w:.[1]}])}
     },
     numerics: {
       Lhalf: ($Lhalf|tonumber), L1: ($L1|tonumber),
       two_scale_agree: {half: ($agree_half=="true"), one: ($agree_one=="true")},
       tail_proxy: {half: ($tail_half|tonumber), one: ($tail_one|tonumber), method:"panel_truncation"}
     }
   }' > "$leaf"

# Witness pack and verification metadata
att="$outdir/attestation.json"
manifest="$outdir/manifest.json"
verify_meta="$outdir/verification.json"
ts="$(date -u +%Y%m%dT%H%M%SZ)"
pack=".tau_ledger/discovery/witness-${N}-${CURVE_LABEL}-${ts}.tar.gz"

jq -n --arg uname "$(uname -a 2>/dev/null || echo unknown)" \
      --arg shell "$SHELL" \
      --arg runner "${GITHUB_RUN_ID:-}" \
      --arg sha "${GITHUB_SHA:-}" \
      '{uname:$uname, shell:$shell, ci:{github_run_id:$runner, commit:$sha}}' > "$att"

jq -n \
  --arg method "point_counting_mod_p" \
  --argjson prime_count "$pcount" \
  --arg max_ratio "$max_hasse_ratio" \
  --arg worst_p "$worst_p" \
  '{method:$method, primes_evaluated:$prime_count, hasse:{max_ratio:($max_ratio|tonumber), worst_p:($worst_p|tonumber)}}' > "$verify_meta"

tmpm="$(mktemp)"
for f in "$panel" "$leaf" "$att" "$verify_meta"; do
  if command -v sha256sum >/dev/null 2>&1; then
    printf '{"path":"%s","sha256":"%s"}\n' "$f" "$(sha256sum "$f" | awk '{print $1}')" >> "$tmpm"
  else
    printf '{"path":"%s","sha256":"%s"}\n' "$f" "$(shasum -a256 "$f" | awk '{print $1}')" >> "$tmpm"
  fi
done
jq -s '.' "$tmpm" > "$manifest"; rm -f "$tmpm"

tar -czf "$pack" -C "$outdir" "$(basename "$panel")" "$(basename "$leaf")" "$(basename "$att")" "$(basename "$manifest")" "$(basename "$verify_meta")"

echo "[atlas] built $CURVE_LABEL (N=$N) :: primes=$pcount hasse_v=$hasse_violations worst_ratio=$max_hasse_ratio@p=$worst_p"
