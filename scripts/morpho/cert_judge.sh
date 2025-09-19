#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
cert="${1:-}"; [ -f "$cert" ] || { echo "usage: cert_judge.sh CERT.json" >&2; exit 2; }
eps="${EPS:-1e-6}"

num () { awk 'BEGIN{ok=0} {if($0 ~ /^([+-]?[0-9]*\.?[0-9]+([eE][+-]?[0-9]+)?)$/){ok=1}} END{exit ok?0:1}'; }
jnum () { awk 'match($0,/"'"$1"'":[[:space:]]*([-+0-9.eE]+)/,m){print m[1]; exit} END{if(NR==0) exit 1}'; }
fpeq () { awk -v a="$1" -v b="$2" -v e="$3" 'BEGIN{da=a-b; if(da<0) da=-da; exit (da<=e)?0:1}'; }

# Extract numeric h_bar
hbar_cert="$(jnum h_bar < "$cert" 2>/dev/null || true)"
[ -n "$hbar_cert" ] && printf '%s' "$hbar_cert" | num >/dev/null || { echo "bad cert: missing/invalid h_bar"; exit 3; }

# Extract locals count (optional)
locals_cert="$(awk 'match($0,/"locals":[[:space:]]*([0-9]+)/,m){print m[1]; exit}' "$cert" 2>/dev/null || true)"
[ -n "$locals_cert" ] || locals_cert=0

mapfile -t LOCALS < <(ls -1 .tau_ledger/morpho/*.local 2>/dev/null || true)
[ ${#LOCALS[@]} -ge 1 ] || { echo "no .local files found"; exit 4; }

# Verify each local quickly
for lf in "${LOCALS[@]}"; do
  SRC="$(awk -F= '/^SRC=/{print $2}' "$lf" | head -n1)"
  SHA="$(awk -F= '/^SHA256=/{print $2}' "$lf" | head -n1)"
  [ -n "$SRC" ] && [ -n "$SHA" ] || { echo "missing SRC/SHA256 in $(basename "$lf")"; exit 5; }
  [ -f "$SRC" ] || { echo "SRC not found: $SRC (from $(basename "$lf"))"; exit 6; }
  cursha="$(sha256sum "$SRC" | awk '{print $1}')"
  [ "$cursha" = "$SHA" ] || { echo "hash mismatch in $(basename "$lf"): want=$SHA got=$cursha"; exit 7; }
  # check H consistency if EVEN/ODD are present
  EVEN="$(awk -F= '/^EVEN=/{print $2}' "$lf" | head -n1)"
  ODD="$(awk -F= '/^ODD=/{print $2}'   "$lf" | head -n1)"
  H_L="$(awk -F= '/^H=/{print $2}'     "$lf" | head -n1)"
  if [ -n "$EVEN" ] && [ -n "$ODD" ] && printf '%s\n' "$EVEN" | num && printf '%s\n' "$ODD" | num; then
    H_calc="$(awk -v e="$EVEN" -v o="$ODD" 'BEGIN{t=e+o; if(t==0) print "0"; else printf "%.8f", e/t}')"
    if [ -n "$H_L" ] && printf '%s\n' "$H_L" | num; then
      fpeq "$H_L" "$H_calc" "$eps" || { echo "H mismatch in $(basename "$lf"): have=$H_L calc=$H_calc"; exit 8; }
    fi
  fi
done

# Recompose and compare H_BAR
tmpG=".tau_ledger/morpho/.judge_global.$$"
scripts/geom/l_series_compose.sh "$tmpG" "${LOCALS[@]}" >/dev/null
hbar_new="$(awk -F= '/^H_BAR=/{print $2}' "$tmpG" | head -n1)"
printf '%s' "$hbar_new" | num >/dev/null || { echo "global replay: invalid H_BAR"; rm -f "$tmpG"; exit 10; }
fpeq "$hbar_new" "$hbar_cert" "$eps" || { echo "H_BAR mismatch: cert=$hbar_cert replay=$hbar_new (eps=$eps)"; rm -f "$tmpG"; exit 11; }

rm -f "$tmpG"
echo "judge: OK — $(basename "$cert") verified (H_BAR=$hbar_cert; locals=${#LOCALS[@]})"
