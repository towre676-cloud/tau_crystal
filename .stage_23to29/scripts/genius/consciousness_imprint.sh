#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
. scripts/genius/_util.sh

root=".tau_ledger/genius"; mkdir -p "$root"
t=$(ts); id="consciousv1-$t"; meta="$root/$id.meta"

# collect tau values (normalize CRLF just in case)
mapfile -t TAUS < <(sed -n 's/^tau: //p' "$root"/entangle-*.meta 2>/dev/null | tr -d '\r' || true)
cnt=${#TAUS[@]}

: > "$meta"
emit_kv "schema" "taucrystal/conscious/v1" "$meta"
emit_kv "id" "$id" "$meta"
emit_kv "utc" "$t" "$meta"

if [ "$cnt" -eq 0 ]; then
  emit_kv "variance" "nan" "$meta"
  emit_kv "is_deterministic" "0" "$meta"
  echo "[warn] conscious: no tau values (run gen_entangle first)"
  exit 0
fi

# mean and variance via awk (stable on Git Bash)
stats=$(printf '%s\n' "${TAUS[@]}" | awk '
  { n++; x+=$1; xs+=$1*$1 }
  END {
    if(n==0){ print "0 0 0" }
    else {
      m=x/n; v=xs/n - m*m; if(v<0){v=0}; printf "%d %.12f %.12f\n", n, m, v
    }
  }')

read n mean var <<<"$stats"

emit_kv "mean" "$mean" "$meta"
emit_kv "variance" "$var" "$meta"

# deterministic if variance < 1e-3
det=$(awk -v v="$var" 'BEGIN{print (v<0.001)?1:0}')
emit_kv "is_deterministic" "$det" "$meta"

if [ "$det" = "1" ]; then
  echo "[OK] conscious: variance=$var (deterministic)"
else
  echo "[warn] conscious: variance=$var (non-deterministic)"
fi

# always soft-exit OK (our style)
exit 0
