#!/usr/bin/env bash
# Verify a zkdiff-lite proof against working tree.
set -Eeuo pipefail; set +H; umask 022
proof="${1:-}"; [ -n "$proof" ] && [ -f "$proof" ] || { echo "usage: $0 <proof-file>"; exit 2; }
sha(){ scripts/meta/_sha256.sh "$1"; }

base="$(grep '^base_listing:' "$proof" | awk '{print $2}')"
basefile=".tau_ledger/zkdiff/$base"
[ -f "$basefile" ] || { echo "[ERR] missing baseline listing: $basefile"; exit 2; }
want="$(grep '^new_ladder_sha256:' "$proof" | awk '{print $2}')"

# declared changed paths
mapfile -t claim < <(awk '/^changed_paths:/{for(i=2;i<=NF;i++)print $i}' "$proof")

# load base order + old hashes
declare -A old; declare -a order
while IFS= read -r line; do
  h="${line%%  *}"; p="${line#*  }"
  old["$p"]="$h"; order+=("$p")
done < "$basefile"

# extend order with any claimed path not present (added files)
for c in "${claim[@]}"; do
  if [ -z "${old[$c]:-}" ]; then
    old["$c"]="__MISSING__"
    order+=("$c")
  fi
done

# compute current hashes; determine changed set
declare -A new changed
for p in "${order[@]}"; do
  if [ -f "$p" ]; then nh="$(sha "$p")"; else nh="__MISSING__"; fi
  new["$p"]="$nh"
  [ "${old[$p]}" != "$nh" ] && changed["$p"]=1 || true
done

# ensure changed set == claim set
declare -A claimset; for c in "${claim[@]:-}"; do claimset["$c"]=1; done
for p in "${!changed[@]}"; do [ -n "${claimset[$p]:-}" ] || { echo "[FAIL] extra change not claimed: $p"; exit 1; }; done
for p in "${!claimset[@]}"; do [ -n "${changed[$p]:-}" ] || { echo "[FAIL] claimed but unchanged: $p"; exit 1; }; done

# authenticate per-claim old/new hashes match working tree & baseline
for p in "${claim[@]}"; do
  # extract old/new from proof block for this path
  po="$(awk -v P="$p" '$0=="  "P{getline; if($1=="old:") print $2}' "$proof")"
  pn="$(awk -v P="$p" '$0=="  "P{getline; getline; if($1=="new:") print $2}' "$proof")"
  [ "$po" = "${old[$p]}" ] || { echo "[FAIL] old hash mismatch for $p"; exit 1; }
  [ "$pn" = "${new[$p]}" ] || { echo "[FAIL] new hash mismatch for $p"; exit 1; }
done

# recompute ladder over extended order
ladder=""
for p in "${order[@]}"; do
  ladder="$(printf '%s\n%s  %s' "$ladder" "${new[$p]}" "$p" | openssl dgst -sha256 | awk '{print $2}')"
done

[ "$ladder" = "$want" ] || { echo "[FAIL] ladder mismatch"; echo " want: $want"; echo " have: $ladder"; exit 1; }
echo "[OK] zkdiff-lite proof verified"
