#!/usr/bin/env bash
set -Eeuo pipefail; set +H
. scripts/langlands/_bash_math.sh

OUTDIR="analysis/normalized"
mkdir -p "$OUTDIR"

# optional tuned Sym² TSV to count rows
S2_TSV="${S2_TSV:-analysis/sym2_candidates.tuned.tsv}"
S2_COUNT=0
[ -s "$S2_TSV" ] && S2_COUNT=$(( $(wc -l < "$S2_TSV") + 0 ))

norm_one () {
  local f="$1" base out crit turing flag
  base="$(basename "$f")"
  out="$OUTDIR/${base%.json}.norm.json"

  # try to read from JSON-ish fields; gracefully default
  crit="$(grep -Eo '"critical(_line)?_zero[s]?"[[:space:]]*:[[:space:]]*[0-9]+' "$f" 2>/dev/null | tail -n1 | sed -E 's/.*:\s*([0-9]+).*/\1/' || true)"
  case "$crit" in (""|*[!0-9]*) crit=0 ;; esac

  # turing: prefer explicit field if present, else = critical zeros
  turing="$(grep -Eo '"turing"[[:space:]]*:[[:space:]]*[0-9]+' "$f" 2>/dev/null | tail -n1 | sed -E 's/.*:\s*([0-9]+).*/\1/' || true)"
  case "$turing" in (""|*[!0-9]*) turing="$crit" ;; esac

  # flag = crit>0 (boolean JSON)
  if [ "$crit" -gt 0 ]; then flag=true; else flag=false; fi

  # sym2_outside_hits: prefer field; else from tuned TSV count (minus header if any)
  local sym2
  sym2="$(grep -Eo '"sym2(_outside(_strip)?)?_hit[s]?"[[:space:]]*:[[:space:]]*[0-9]+' "$f" 2>/dev/null | tail -n1 | sed -E 's/.*:\s*([0-9]+).*/\1/' || true)"
  case "$sym2" in (""|*[!0-9]*) sym2="$S2_COUNT" ;; esac

  # emit minimal normalized JSON (no jq)
  {
    printf '{\n'
    printf '  "ref": %s,\n' "$(printf '%s' "$f" | sed 's/"/\\"/g; s/.*/"&"/')"
    printf '  "flag": %s,\n' "$flag"
    printf '  "turing": %s,\n' "$turing"
    printf '  "critical_line_zeros": %s,\n' "$crit"
    printf '  "sym2_outside_hits": %s,\n' "$sym2"
    printf '  "generated_at": %s\n' "$(date -u +'"%Y-%m-%dT%H:%M:%SZ"')"
    printf '}\n'
  } > "$out"

  echo "$out"
}

# walk inputs
if [ "$#" -eq 0 ]; then
  set -- .tau_ledger/langlands analysis
fi

for d in "$@"; do
  [ -d "$d" ] || continue
  while IFS= read -r -d '' j; do
    norm_one "$j"
  done < <(find "$d" -type f -name '*.json' -print0 2>/dev/null)
done
