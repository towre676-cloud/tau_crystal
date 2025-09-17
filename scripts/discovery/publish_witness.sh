#!/usr/bin/env bash
set -Ee -o pipefail; set +H; umask 022
sha_file(){
  if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | cut -d" " -f1;
  elif command -v shasum >/dev/null 2>&1; then shasum -a 256 "$1" | cut -d" " -f1;
  else openssl dgst -sha256 "$1" 2>/dev/null | awk "{print \$2}"; fi
}
ts=$(date -u +"%Y%m%dT%H%M%SZ")
root=".tau_ledger/discovery"; mkdir -p "$root"
last_line=$(tail -n1 .tau_ledger/CHAIN 2>/dev/null || true)
[ -n "$last_line" ] || { echo "[witness] no receipt yet"; exit 3; }
rec_path="${last_line#*$'\t'}"
[ -s "$rec_path" ] || { echo "[witness] receipt path missing: $rec_path"; exit 3; }
att=$(ls -1 .tau_ledger/attest/attest-*.json 2>/dev/null | tail -n1 || true)
tmpd=$(mktemp -d) ; trap 'rm -rf "$tmpd"' EXIT
mkdir -p "$tmpd/discovery"
cp -f "$rec_path" "$tmpd/discovery/receipt.json"
if [ -n "$att" ] && [ -s "$att" ]; then cp -f "$att" "$tmpd/discovery/attestation.json"; fi
m="$tmpd/discovery/manifest.json"; : > "$m"
printf "%s\n" "{" >> "$m"
printf "%s\n" "  \"schema\":\"taucrystal/witness/v1\"," >> "$m"
printf "%s\n" "  \"timestamp\":\"$ts\"," >> "$m"
printf "%s\n" "  \"receipt_path\":\"$rec_path\"," >> "$m"
if [ -n "$att" ] && [ -s "$att" ]; then printf "%s\n" "  \"attestation_path\":\"$att\"," >> "$m"; fi
printf "%s"   "  \"files\":[\"receipt.json\"" >> "$m"
if [ -n "$att" ] && [ -s "$att" ]; then printf "%s" ", \"attestation.json\"" >> "$m"; fi
printf "%s\n" "]" >> "$m"
printf "%s\n" "}" >> "$m"
pack="$root/witness-$ts.tar.gz"
tar -C "$tmpd" -czf "$pack" discovery
d=$(sha_file "$pack")
printf "%s\t%s\n" "$d" "$pack" >> "$root/WITNESS_CHAIN"
echo "[witness] minted $pack"
