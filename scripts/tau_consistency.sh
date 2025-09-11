#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022
# Usage: tau_consistency.sh <prompt-file> <baseline-output-file>
# Requires TAU_LLM_CMD for real runs; without it, uses deterministic placeholders.
PF="${1:-}"; BF="${2:-}"; [ -f "$PF" ] && [ -f "$BF" ] || { echo "{\"ok\":false,\"error\":\"usage: tau_consistency.sh <prompt> <baseline_out>\"}"; exit 2; }
variants_dir=$(mktemp -d); trap 'rm -rf "$variants_dir"' EXIT
p_norm(){ tr -d "\r" | sed -Ee "s/[[:space:]]+/ /g" -e "s/^ //; s/ $//"; }
make_variant(){
  mode="$1"; out="$2"; txt="$(cat -- "$PF")";
  case "$mode" in
    syn)   printf "%s" "$txt" | sed -e "s/\\bpropose\\b/suggest/gI" -e "s/\\bexplain\\b/clarify/gI" -e "s/\\bscore\\b/evaluate/gI" > "$out" ;;
    pre)   printf "Given the following, respond precisely:\\n\\n%s" "$txt" > "$out" ;;
    order) printf "%s" "$txt" | awk 'BEGIN{ORS=""} {gsub(/•/,"-"); print} END{print "\n(interpret tasks in strict order)"}' > "$out" ;;
    *)     printf "%s" "$txt" > "$out" ;;
  esac
}
run_llm(){
  infile="$1"; ofile="$2";
  if [ -n "${TAU_LLM_CMD:-}" ]; then cat -- "$infile" | eval "$TAU_LLM_CMD" > "$ofile" 2>/dev/null || true; else printf "PLACEHOLDER_OUTPUT_FOR_%s\n" "$(basename -- "$infile")" > "$ofile"; fi
}
measure(){ bash scripts/tau_semantic.sh "$BF" "$1" 2>/dev/null || echo "{\"ok\":false}"; }
declare -a modes=("syn" "pre" "order")
pass=0; total=0; min_sim="1.000000"; gate_embed=${TAU_BEH_EMBED_MIN:-0.85}; gate_bow=${TAU_BEH_BOW_MIN:-0.75};
details=""; first=1
for m in "${modes[@]}"; do
  v="$variants_dir/$m.prompt"; o="$variants_dir/$m.out"; make_variant "$m" "$v"; run_llm "$v" "$o";
  mjson=$(measure "$o"); cb=$(printf "%s" "$mjson" | sed -n 's/.*"cosine_bow":[ ]*\([0-9.]\+\).*/\1/p'); ce=$(printf "%s" "$mjson" | sed -n 's/.*"cosine_embed":[ ]*\([0-9.]\+\).*/\1/p');
  sim="$cb"; method="bow"; if [ -n "${ce:-}" ]; then sim="$ce"; method="emb"; fi
  total=$((total+1)); pass_gate=0
  if [ -n "${ce:-}" ]; then awk -v s="$sim" -v g="$gate_embed" 'BEGIN{exit !(s>=g)}' && pass_gate=1; else awk -v s="$sim" -v g="$gate_bow" 'BEGIN{exit !(s>=g)}' && pass_gate=1; fi
  [ "$pass_gate" -eq 1 ] && pass=$((pass+1))
  awk -v a="$sim" -v b="$min_sim" 'BEGIN{if(a<b) print a; else print b}' > "$variants_dir/min.tmp"; min_sim="$(cat "$variants_dir/min.tmp")"
  [ $first -eq 1 ] && first=0 && details="{\"variant\":\"\",\"sim\":$sim,\"method\":\"$method\"}" || details="$details,{\"variant\":\"\",\"sim\":$sim,\"method\":\"$method\"}"
done
rate=$(awk -v p="$pass" -v t="$total" 'BEGIN{if(t==0){print "0.0"} else {printf "%.6f\n", (p+0.0)/t}}')
printf "{\"ok\":true,\"consistency_rate\":%s,\"variants\":%s,\"min_similarity\":%s,\"details\":[%s]}\n" "$rate" "$total" "$min_sim" "$details"
