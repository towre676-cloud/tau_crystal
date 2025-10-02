#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
outdir=".tau_ledger/signature"; mkdir -p "$outdir"
stamp=$(date -u +%Y%m%dT%H%M%SZ); id="sigv1-$stamp"; json="$outdir/$id.json"
: > "$json"
printf "%s\n" "{" >> "$json"
printf "%s\n" "  \"schema\": \"taucrystal/signature/v1\"," >> "$json"
printf "%s\n" "  \"id\": \"$id\"," >> "$json"
printf "%s\n" "  \"utc\": \"$stamp\"," >> "$json"
printf "%s\n" "  \"constraints\": [" >> "$json"
i=0
for r in constraints.d/*.rules; do
  [ -s "$r" ] || continue
  i=$((i+1))
  SEP=$([ $i -gt 1 ] && echo "," || true)
  printf "%s\n" "    $SEP{\"file\": \"$(basename "$r")\", \"sha256\": \"$(scripts/meta/_sha256.sh "$r")\"}" >> "$json"
done
printf "%s\n" "  ]" >> "$json"
printf "%s\n" "}" >> "$json"
echo "[OK] signature rules: $json"
