#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022

usage(){ cat <<EOF 2>/dev/null || true
Usage: tau_gate.sh [--strict] [--verbose] file1.json [file2.json ...]
Env (defaults):
  TAU_SEM_EMBED_MIN=0.85   # if cosine_embed present
  TAU_SEM_BOW_MIN=0.75     # fallback threshold
  TAU_CONSIST_MIN=0.67     # minimal consistency_rate
  TAU_REQUIRE_CONSTRAINTS=1   # fail if violations_count>0
  TAU_REQUIRE_ADVERSARIAL=0   # fail if adversarial_pass=false
EOF
}

SEM_EMBED_MIN="${TAU_SEM_EMBED_MIN:-0.85}"
SEM_BOW_MIN="${TAU_SEM_BOW_MIN:-0.75}"
CONSIST_MIN="${TAU_CONSIST_MIN:-0.67}"
REQ_CONS="${TAU_REQUIRE_CONSTRAINTS:-1}"
REQ_ADV="${TAU_REQUIRE_ADVERSARIAL:-0}"
VERBOSE=0

args=()
while [ $# -gt 0 ]; do
  case "${1:-}" in
    -h|--help) usage; exit 0;;
    --verbose) VERBOSE=1; shift;;
    --strict) SEM_EMBED_MIN=0.90; SEM_BOW_MIN=0.80; CONSIST_MIN=0.80; REQ_CONS=1; REQ_ADV=1; shift;;
    -*) echo "[gate] unknown flag: $1" >&2; usage; exit 2;;
    *) args+=("$1"); shift;;
  esac
done
[ ${#args[@]} -gt 0 ] || { usage; exit 2; }

fail_any=0
for f in "${args[@]}"; do
  [ -f "$f" ] || { echo "[gate] missing file: $f" >&2; fail_any=1; continue; }
  data=$(cat -- "$f")
  em=$(printf "%s" "$data" | sed -n 's/.*"cosine_embed":[ ]*\([0-9.][0-9.]*\).*/\1/p' | head -n1 || true)
  bo=$(printf "%s" "$data" | sed -n 's/.*"cosine_bow":[ ]*\([0-9.][0-9.]*\).*/\1/p' | head -n1 || true)
  cr=$(printf "%s" "$data" | sed -n 's/.*"consistency_rate":[ ]*\([0-9.][0-9.]*\).*/\1/p' | head -n1 || true)
  vc=$(printf "%s" "$data" | sed -n 's/.*"violations_count":[ ]*\([0-9][0-9]*\).*/\1/p' | head -n1 || true)
  ap=false; printf "%s" "$data" | grep -qi '"adversarial_pass"[[:space:]]*:[[:space:]]*true' && ap=true
  # defaults when missing:
  [ -n "${vc:-}" ] || vc=0
  [ -n "${cr:-}" ] || cr=0
  if [ -n "${em:-}" ]; then thr="$SEM_EMBED_MIN"; sim="$em"; mode="embed"; else thr="$SEM_BOW_MIN"; sim="${bo:-0}"; mode="bow"; fi
  sim_ok=0; awk -v s="$sim" -v t="$thr" 'BEGIN{exit !(s>=t)}' && sim_ok=1
  if [ "${TAU_DISABLE_PROMPT_SIM:-0}" = "1" ]; then
    sim_ok=1
    echo "[gate] TAU_DISABLE_PROMPT_SIM=1 -> skipping prompt-sim check" >&2
  fi
  if [ "${TAU_DISABLE_PROMPT_SIM:-0}" = "1" ]; then sim_ok=1; mode=mode"(skipped)"; sim="NA"; thr="NA"; else
    awk -v s="$sim" -v t="$thr" 'BEGIN{exit !(s>=t)}' && sim_ok=1
  fi
  cr_ok=0;  awk -v s="$cr"  -v t="$CONSIST_MIN" 'BEGIN{exit !(s>=t)}' && cr_ok=1
  cons_ok=1; [ "$REQ_CONS" -eq 1 ] && [ "$vc" -gt 0 ] && cons_ok=0
  adv_ok=1; [ "$REQ_ADV" -eq 1 ] && [ "$ap" != true ] && adv_ok=0
  [ "$VERBOSE" -eq 1 ] && echo "[gate] $f :: sim()= thr= ok=$sim_ok; consistency=$cr thr=$CONSIST_MIN ok=$cr_ok; violations=$vc ok=$cons_ok; adversarial=$ap ok=$adv_ok"
  if [ $sim_ok -eq 1 ] && [ $cr_ok -eq 1 ] && [ $cons_ok -eq 1 ] && [ $adv_ok -eq 1 ]; then
    [ "$VERBOSE" -eq 1 ] && echo "[gate] PASS: $f"
  else
    echo "[gate] FAIL: $f" >&2; fail_any=1
  fi
done
exit "$fail_any"
