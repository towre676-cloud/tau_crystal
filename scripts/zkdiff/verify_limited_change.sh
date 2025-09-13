#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
proof="${1:-}"; [ -n "$proof" ] && [ -f "$proof" ] || { echo "usage: $0 <proof-file>"; exit 2; }
sha(){ scripts/meta/_sha256.sh "$1"; }

base="$(awk '/^base_listing:/{print $2}' "$proof")"
want="$(awk '/^new_ladder_sha256:/{print $2}' "$proof")"
[ -n "$base" ] && [ -n "$want" ] || { echo "[ERR] malformed proof"; exit 2; }
basefile=".tau_ledger/zkdiff/$base"
[ -f "$basefile" ] || { echo "[ERR] missing baseline listing: $basefile"; exit 2; }

# claim list
mapfile -t claim < <(awk '/^changed_paths:/{for(i=2;i<=NF;i++)print $i}' "$proof")

# load baseline order + old hashes
declare -A old; order=()
while IFS= read -r line; do
  h="${line%%  *}"; p="${line#*  }"
  [ -n "$p" ] || continue
  old["$p"]="$h"; order+=("$p")
done < "$basefile"

# extend with additions
for c in "${claim[@]}"; do
  if [ -z "${old[$c]:-}" ]; then
    old["$c"]="__MISSING__"
    order+=("$c")
  fi
done

# recompute current hashes and changed set
declare -A new changed
for p in "${order[@]}"; do
  if [ -f "$p" ]; then nh="$(sha "$p")"; else nh="__MISSING__"; fi
  new["$p"]="$nh"
  [ "${old[$p]}" != "$nh" ] && changed["$p"]=1 || true
done

# set equality
declare -A claimset; for c in "${claim[@]:-}"; do claimset["$c"]=1; done
for p in "${!changed[@]}"; do [ -n "${claimset[$p]:-}" ] || { echo "[FAIL] extra change not claimed: $p"; exit 1; }; done
for p in "${!claimset[@]}"; do [ -n "${changed[$p]:-}" ] || { echo "[FAIL] claimed but unchanged: $p"; exit 1; }; done

# verify per-claim old/new hashes match proof lines
for p in "${claim[@]}"; do
  po="$(awk -v P="$p" '$0=="  "P{getline; if($1=="old:") print $2}' "$proof")"
  pn="$(awk -v P="$p" '$0=="  "P{getline; getline; if($1=="new:") print $2}' "$proof")"
  [ "$po" = "${old[$p]}" ] || { echo "[FAIL] old hash mismatch for $p"; exit 1; }
  [ "$pn" = "${new[$p]}" ] || { echo "[FAIL] new hash mismatch for $p"; exit 1; }
done

# recompute ladder
ladder=""
for p in "${order[@]}"; do
  ladder="$(printf '%s\n%s  %s' "$ladder" "${new[$p]}" "$p" | tr -d '\r' | sha256sum | awk '{print $1}')"
done

[ "$ladder" = "$want" ] || { echo "[FAIL] ladder mismatch"; echo " want: $want"; echo " have: $ladder"; exit 1; }
echo "[OK] zkdiff-lite proof verified"
