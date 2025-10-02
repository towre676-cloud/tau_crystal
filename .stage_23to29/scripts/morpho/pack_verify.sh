#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
pack="${1:-}"; [ -d "$pack" ] || { echo "usage: pack_verify.sh PACK_DIR"; exit 2; }
rec="$pack/corridor.receipt.tsv"; [ -f "$rec" ] || { echo "missing corridor.receipt.tsv"; exit 3; }

# 1) hash check (no pipelines; skip the receipt itself)
ok=1
while read -r tag name hash; do
  [ "$tag" = "SHA256" ] || continue
  [ "$name" = "corridor.receipt.tsv" ] && continue
  f="$pack/$name"
  if [ ! -f "$f" ]; then
    echo "missing $name"; ok=0; break
  fi
  cur=$(sha256sum "$f" | awk '{print $1}')
  if [ "$cur" != "$hash" ]; then
    echo "hash mismatch for $name"; echo "want=$hash got=$cur"
    ok=0; break
  fi
done < "$rec"
[ $ok -eq 1 ] || exit 5
echo "hashes OK"

# 2) stage locals/global for judge
tmp=".tau_ledger/.verify_$$"; rm -rf "$tmp"; mkdir -p "$tmp/morpho"
find "$pack" -maxdepth 1 -name "*.local" -exec cp -f {} "$tmp/morpho/" \;
[ -f "$pack/global.L" ] && cp -f "$pack/global.L" "$tmp/morpho/" || true

# 3) pick newest cert in the pack
shopt -s nullglob
files=( "$pack"/cert_*.json )
[ ${#files[@]} -gt 0 ] || { echo "no cert in pack"; exit 6; }
latest="${files[0]}"; for f in "${files[@]}"; do [ "$f" -nt "$latest" ] && latest="$f"; done

# 4) swap in staged ledger and judge
save=".tau_ledger/.save_morpho_$$"
if [ -d ".tau_ledger/morpho" ]; then mv ".tau_ledger/morpho" "$save"; fi
mkdir -p ".tau_ledger"; mv "$tmp/morpho" ".tau_ledger/morpho"
scripts/morpho/cert_judge.sh "$latest"; rc=$?
rm -rf ".tau_ledger/morpho"; [ -d "$save" ] && mv "$save" ".tau_ledger/morpho" || true
rm -rf "$tmp"
exit $rc
