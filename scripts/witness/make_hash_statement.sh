#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022
die(){ echo "[witness] ERROR: $*" >&2; exit 1; }
ID="${1:?usage: make_hash_statement.sh <capsule-id> <affiant_name> <title> <address>}"; AFF="${2:?}"; TIT="${3:?}"; ADR="${4:?}"
TAR="analysis/capsules/$ID/$ID.tar.gz"; [ -f "$TAR" ] || die "Missing capsule tar: $TAR. Run scripts/ops/attested_delivery.sh \"$ID\" first."
hash_file(){
  if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | tr -d "\r" | cut -d" " -f1; return; fi
  if command -v certutil   >/dev/null 2>&1; then certutil -hashfile "$(cygpath -w "$1" 2>/dev/null || echo "$1")" SHA256 2>/dev/null | sed -n "2p" | tr -d " \r\n"; return; fi
  die "No sha256 tool found (need sha256sum or certutil)."
}
H=$(hash_file "$TAR"); [ -n "$H" ] || die "Empty SHA-256 hash for $TAR"
printf "%s" "$H" | grep -Eq "^[A-Fa-f0-9]{64}$" || die "Computed hash does not look like SHA-256: $H"
if SIZE=$(wc -c < "$TAR" 2>/dev/null); then SIZE=$(echo "$SIZE" | tr -d " "); else SIZE=$(stat -c%s "$TAR" 2>/dev/null || stat -f%z "$TAR" 2>/dev/null || die "Could not stat $TAR"); fi
SEAL=$(date -u +%Y-%m-%dT%H:%M:%SZ)
TXT="docs/witness/$ID.hash.txt"; : > "$TXT"
printf "Hash Statement – Capsule %s\n" "$ID" >> "$TXT"
printf "SHA-256: %s\n" "$H" >> "$TXT"
printf "File:    %s\n" "$TAR" >> "$TXT"
printf "Size:    %s bytes\n" "$SIZE" >> "$TXT"
printf "Sealed:  %s UTC (gates verified)\n" "$SEAL" >> "$TXT"
printf "Affiant: %s, %s, %s\n" "$AFF" "$TIT" "$ADR" >> "$TXT"
LEDGER=".tau_ledger/witness/jurisdictional/$ID.json"; : > "$LEDGER"
printf "%s\n" "{" >> "$LEDGER"
printf "%s\n" "  \"capsule\":\"$ID\"," >> "$LEDGER"
