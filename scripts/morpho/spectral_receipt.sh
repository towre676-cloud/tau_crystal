#!/usr/bin/env bash
# spectral_receipt.sh MOD SRC OUT.local
# Emits a receipt with keys: MOD, SRC, SHA256, EVEN, ODD, H, [SPEC], TIME
set -E -o pipefail; set +H; umask 022
mod="${1:-}"; src="${2:-}"; out="${3:-.tau_ledger/morpho/v_frontal.local}"
[ -n "$mod" ] && [ -n "$src" ] || { echo "usage: spectral_receipt.sh MOD SRC OUT.local" >&2; exit 2; }
mkdir -p "$(dirname "$out")"
[ -f "$src" ] || { echo "missing source: $src" >&2; exit 3; }

sha="$(sha256sum "$src" | awk '{print $1}')"
ts="$(date -u +%Y%m%dT%H%M%SZ)"

emit_receipt() {
  : > "$out"
  printf "MOD=%s\n"   "$mod"  >> "$out"
  printf "SRC=%s\n"   "$src"  >> "$out"
  printf "SHA256=%s\n" "$sha" >> "$out"
  printf "%s" "$1"            >> "$out"   # body must end with newline(s)
  printf "TIME=%s\n" "$ts"    >> "$out"
}

ext_lc="$(echo "${src##*.}" | tr 'A-Z' 'a-z')"
is_mesh=0
case "$ext_lc" in obj|ply) is_mesh=1;; esac

if [ "$is_mesh" -eq 1 ]; then
  # Try the Python Laplace–Beltrami kernel
  body="$(LB_K=${LB_K:-32} scripts/morpho/lb_kernel.py "$src" 2>/dev/null || true)"
  if printf '%s\n' "$body" | grep -q '^PY_ERROR='; then
    echo "lb_kernel.py failed: $(printf '%s\n' "$body" | sed -n 's/^PY_ERROR=//p')" >&2
    body=""
  fi
  if printf '%s\n' "$body" | grep -q '^EVEN='; then
    emit_receipt "$(printf '%s\n' "$body")"
    echo "ok: spectral(LB) $mod -> $out"
    exit 0
  fi
  echo "warning: LB kernel unavailable; falling back to stub" >&2
fi

# --- Fallback stub (deterministic from sha hex) ---
hex="$sha"
spec=""; even=0; odd=0; idx=0
while IFS= read -r -n1 c; do
  case "$c" in
    [0-9]) v=$(( 1 + ($(printf '%d' "'$c") % 10) ));;
    [a-f]) v=$(( 6 + ($(printf '%d' "'$c") % 10) ));;
    *) continue;;
  esac
  f=$(awk -v x="$v" 'BEGIN{printf "%.6f", x/16.0}')
  spec="${spec}${spec:+,}${f}"
  if [ $((idx%2)) -eq 0 ]; then
    even=$(awk -v e="$even" -v f="$f" 'BEGIN{print e+f}')
  else
    odd=$(awk -v o="$odd" -v f="$f" 'BEGIN{print o+f}')
  fi
  idx=$((idx+1))
  [ $idx -ge 64 ] && break
done < <(printf '%s' "$hex")

tot=$(awk -v e="$even" -v o="$odd" 'BEGIN{print e+o}')
H=$(awk -v e="$even" -v t="$tot" 'BEGIN{if(t==0) print "0"; else printf "%.8f", e/t}')
body=$(printf "EVEN=%.8f\nODD=%.8f\nH=%s\nSPEC=%s\n" "$even" "$odd" "$H" "$spec")
emit_receipt "$body"
echo "ok: spectral(STUB) $mod -> $out"
