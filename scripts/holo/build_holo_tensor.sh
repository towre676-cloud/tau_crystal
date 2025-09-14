#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
root=".tau_ledger/holo"; mkdir -p "$root"
stamp=$(date -u +%Y%m%dT%H%M%SZ); id="holov1-$stamp"; json="$root/$id.json"
mapfile -t receipts < <(ls -1 .tau_ledger/receipts/*.json 2>/dev/null | LC_ALL=C sort || true)
[ "${#receipts[@]}" -gt 0 ] || { echo "[err] no receipts found"; exit 2; }
: > "$json"
printf "%s\n" "{" >> "$json"
printf "%s\n" "  \"schema\": \"taucrystal/holo/v1\"," >> "$json"
printf "%s\n" "  \"id\": \"$id\"," >> "$json"
printf "%s\n" "  \"utc\": \"$stamp\"," >> "$json"
printf "%s\n" "  \"tensor\": [" >> "$json"
i=0
for r in "${receipts[@]}"; do
  i=$((i+1))
  sha=$(scripts/meta/_sha256.sh "$r")
  commit=$(jq -r ".commit // \"none\"" "$r" 2>/dev/null || echo "none")
  merkle=$(jq -r ".merkle_root // \"none\"" "$r" 2>/dev/null || echo "none")
  entropy=$(jq -r ".entropy_delta_bytes // 0" "$r" 2>/dev/null || echo 0)
  SEP=$([ $i -gt 1 ] && echo "," || true)
  printf "%s\n" "    $SEP{\"file\": \"$(basename "$r")\", \"sha256\": \"$sha\", \"commit\": \"$commit\", \"merkle_root\": \"$merkle\", \"entropy_delta\": $entropy}" >> "$json"
done
printf "%s\n" "  ]" >> "$json"
printf "%s\n" "}" >> "$json"
echo "[OK] holo tensor: $json"
