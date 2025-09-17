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

# local root numbers (known multiplicative, p>=5)
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

# exact a_p on good primes + Hasse diagnostics
for ((p=3; p<=pmax; p+=2)); do
  is_prime "$p" || continue
  if [ $(( DELTA % p )) -eq 0 ]; then continue; fi
  np=$(count_points_mod_p "$A1" "$A2" "$A3" "$A4" "$A6" "$p")
  ap=$(( p + 1 - np ))
  printf "%d\t%d\n" "$p" "$ap" >> "$panel"
  pcount=$((pcount+1))

  apabs=$(( ap<0 ? -ap : ap ))
  num=$(( apabs*apabs ))
  den=$(( 4*p ))
  r=$(awk -v n="$num" -v d="$den" 'BEGIN{printf "%.6f", (d? n/d : 0)}')
  cmp=$(awk -v r="$r" -v m="$max_hasse_ratio" 'BEGIN{print (r>m)?1:0}')
  [ "$cmp" -eq 1 ] && { max_hasse_ratio="$r"; worst_p="$p"; }
  [ $num -gt $den ] && hasse_violations=$((hasse_violations+1))
done

# Euler product L(s) over panel using awk log/exp; dual truncations for a stability check
euler_L_product_cut(){
  # s in {0.5,1}; cutoff is number of rows to use (excluding header)
  local s="$1" panel="$2" cutoff="$3"
  awk -v s="$s" -v CUT="$cutoff" '
    BEGIN{FS="\t"; sumlog=0; used=0}
    NR==1{next}
    {
      if(used>=CUT) { next }
      p=$1+0; ap=$2+0
      if(s==0.5){ den=(2.0 - ap/sqrt(p)) } else { den=(1.0 - ap/p + 1.0/p) }
      if(den<=0){ den=1e300 }
      sumlog += -log(den)
      used++
    }
    END{ printf "%.16f", exp(sumlog) }
  ' "$panel"
}

rows=$(awk 'END{print NR-1}' "$panel")
cut_full="$rows"
cut_trim=$(( rows*80/100 )); [ "$cut_trim" -lt 5 ] && cut_trim="$rows"

Lhalf_full=$(euler_L_product_cut 0.5 "$panel" "$cut_full")
L1_full=$(euler_L_product_cut 1 "$panel" "$cut_full")
Lhalf_trim=$(euler_L_product_cut 0.5 "$panel" "$cut_trim")
L1_trim=$(euler_L_product_cut 1 "$panel" "$cut_trim")

agree_half=$([ "$Lhalf_full" = "$Lhalf_trim" ] && echo true || echo false)
agree_one=$([ "$L1_full" = "$L1_trim" ] && echo true || echo false)

# crude tail proxies (upper envelopes) beyond max p to 10k
tail_half=$(awk -v P="$pmax" 'BEGIN{sum=0; for(n=P+1;n<=10000;n++){sum+=2/sqrt(n)} printf "%.6f", sum }')
tail_one=$(awk -v P="$pmax" 'BEGIN{sum=0; for(n=P+1;n<=10000;n++){sum+=2/n} printf "%.6f", sum }')

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
  --arg Lhalf "$Lhalf_full" --arg L1 "$L1_full" \
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
       tail_proxy: {half: ($tail_half|tonumber), one: ($tail_one|tonumber), method:"panel_truncation_awk"}
     }
   }' > "$leaf"

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

jq -n --arg method "point_counting_mod_p" \
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
