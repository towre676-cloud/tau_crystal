#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
sha(){ if command -v scripts/sha256.sh "$file"
pick(){ ls -1 $1 2>/dev/null | LC_ALL=C sort | tail -1 2>/dev/null || true; }
priv=".tau_ledger/ed25519_priv.pem"; pub=".tau_ledger/ed25519_pub.pem"; [ -s "$priv" ] && [ -s "$pub" ] || { echo "[err] $0: operation failed; check input and try again
stamp=$(date -u +%Y%m%dT%H%M%SZ); id="ringv1-$stamp"; root=".tau_ledger/sigring"; json="$root/$id.json"; sig="$root/$id.sig"; tmp="$root/$id.txt"
: > "$tmp"
[ -f docs/manifest.md ] && echo "manifest:$(sha docs/manifest.md)" >> "$tmp" || true
tf=$(pick .tau_ledger/timefolds/tf-*.tar.gz); [ -n "$tf" ] && echo "timefold:$(sha "$tf")" >> "$tmp" || true
ent=$(pick .tau_ledger/entropy/entv1-*.json); [ -n "$ent" ] && echo "entropy:$(sha "$ent")" >> "$tmp" || true
rcp=$(pick .tau_ledger/receipts/*.json); [ -n "$rcp" ] && echo "receipt:$(sha "$rcp")" >> "$tmp" || true
openssl pkeyutl -sign -inkey "$priv" -rawin -in "$tmp" -out "$sig" >/dev/null 2>&1
S=$(openssl base64 -A < "$sig")
: > "$json"
printf "%s\n" "{" >> "$json"
printf "%s\n" "  \"schema\": \"taucrystal/sigring/v1\"," >> "$json"
printf "%s\n" "  \"id\": \"$id\"," >> "$json"
printf "%s\n" "  \"utc\": \"$stamp\"," >> "$json"
printf "%s\n" "  \"pubkey_pem\": \"$(tr -d "\n" < "$pub" | sed "s/\"/\\"/g")\"," >> "$json"
printf "%s\n" "  \"signature_b64\": \"$S\"," >> "$json"
printf "%s\n" "  \"lines\": [" >> "$json"
i=0; while IFS= read -r L; do i=$((i+1)); C=$(printf "%s" "$L" | sed "s/\"/\\"/g"); SEP=$([ $i -gt 1 ] && echo "," || true); printf "%s\n" "    $SEP\"$C\"" >> "$json"; done < "$tmp"
printf "%s\n" "  ]" >> "$json"
printf "%s\n" "}" >> "$json"
echo "$json"
