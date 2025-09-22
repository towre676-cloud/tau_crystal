#!/usr/bin/env bash
set -E -o pipefail; set +H
. scripts/langlands/minimal_tau.sh 2>/dev/null || true

sig() {
  local out a b
  out="$(
    scripts/langlands/minimal_tau.sh dir_signature "$@" 2>/dev/null \
      | tr -d '\r' | tr '\t' ' ' | tr -s ' ' | sed -e 's/^ *//' -e 's/ *$//'
  )"
  set -- $out; a="${1:-}"; b="${2:-}"
  case "$a" in -[0-9]*|[0-9]*) : ;; *) a=0 ;; esac
  case "$b" in -[0-9]*|[0-9]*) : ;; *) b=0 ;; esac
  if [ "$a" = 0 ] && [ "$b" = 0 ]; then
    set -- $(scripts/langlands/dirsig_fallback.sh "$@"); a="$1"; b="$2"
  fi
  printf '%s %s\n' "$a" "$b"
}

A="${1:-.tau_ledger}"; B="${2:-.tau_ledger/demo}"
OUT="${3:-.tau_ledger/automorphic/new_zeros.json}"
ENV="analysis/reciprocity_best.env"; [ -f "$ENV" ] || { echo "[err] missing $ENV"; exit 3; }
. "$ENV"
S="${BEST_S_MICRO:-}"; [ -n "$S" ] || { echo "[err] BEST_S_MICRO missing"; exit 4; }
A_OP="${A_OP:-hecke}"
T_MIN="${T_MIN:--400000}"; T_MAX="${T_MAX:-400000}"; T_STEP="${T_STEP:-500}"; REFINE="${REFINE:-18}"

micro_to_dec(){ local x="$1" s=""; [ "$x" -lt 0 ] && s="-" && x=$(( -x )); printf "%s%d.%06d" "$s" $((x/1000000)) $((x%1000000)); }
sgn(){ local d="$1"; [ "$d" -lt 0 ] && echo -1 || { [ "$d" -gt 0 ] && echo 1 || echo 0; }; }

read sA nA <<<"$(sig "$A_OP" "$A")"; [ "$nA" -gt 0 ] || nA=1; mA=$(( sA / nA ))

tmp="$(mktemp)"; : > "$tmp"
prevT=""; prevD=""; T="$T_MIN"; steps=0
while :; do
  read sB nB <<<"$(sig theta "$B" "$S" "$T")"; [ "$nB" -gt 0 ] || nB=1
  mB=$(( sB / nB )); D=$(( mB - mA ))
  if [ -n "$prevD" ]; then
    ps="$(sgn "$prevD")"; cs="$(sgn "$D")"
    if [ "$ps" -ne 0 ] && [ "$cs" -ne 0 ] && [ $(( ps * cs )) -lt 0 ]; then
      lo="$prevT"; hi="$T"; i=0
      while [ "$i" -lt "$REFINE" ]; do
        mid=$(( (lo + hi) / 2 ))
        read sB nB <<<"$(sig theta "$B" "$S" "$mid")"; [ "$nB" -gt 0 ] || nB=1
        dm=$(( (sB / nB) - mA ))
        [ "$dm" -eq 0 ] && { lo="$mid"; hi="$mid"; break; }
        if [ $(( $(sgn "$dm") * $(sgn "$(( (sB/nB) - mA ))") )) -le 0 ] 2>/dev/null; then
          : # keep branch; no extra heuristic divergence check to keep it simple
        fi
        if [ $(( $(sgn "$dm") * $(sgn "$(( ( $(sig theta "$B" "$S" "$lo" | awk '{print $1/$2}') ) - mA ))") )) -le 0 ] 2>/dev/null; then
          hi="$mid"
        else
          lo="$mid"
        fi
        i=$(( i + 1 ))
      done
      echo $(( (lo + hi) / 2 )) >> "$tmp"
    fi
  fi
  prevT="$T"; prevD="$D"
  [ "$T" -ge "$T_MAX" ] && break
  T=$(( T + T_STEP ))
  steps=$(( steps + 1 ))
  if [ $(( steps % 800 )) -eq 0 ]; then printf '.' >&2; fi
done; echo >&2

sort -n "$tmp" | awk -v w=$((2*T_STEP)) 'NR==1{last=$1;print last;next}{d=$1-last;if(d<0)d=-d;if(d>w){print $1;last=$1}}' > "${tmp}.uniq"

ts="$(date -u +%Y-%m-%dT%H:%M:%SZ)"
printf '{"provenance":{"machine":"%s","run_id":"crit_sweep:%s","timestamp":"%s"},"zeros":[' \
  "${COMPUTERNAME:-${HOSTNAME:-local}}" "$ts" "$ts" > "$OUT"
first=1
while IFS= read -r tm; do
  [ -z "$tm" ] && continue
  tdec="$(micro_to_dec "$tm")"
  if [ "$first" -eq 1 ]; then first=0; printf '%s' "$tdec" >> "$OUT"; else printf ',%s' "$tdec" >> "$OUT"; fi
done < "${tmp}.uniq"
printf ']}\n' >> "$OUT"
rm -f "$tmp" "${tmp}.uniq" 2>/dev/null || true
echo "[crit] wrote $OUT"
