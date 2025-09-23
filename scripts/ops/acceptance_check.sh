#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022
TAR="${1:?usage: acceptance_check.sh <tar.gz> <sha256-file> <receipt.json> <minisign_pub>}"; SHA_FILE="${2:?}"; REC="${3:?}"; PUB="${4:?}"
die(){ echo "[accept] ERROR: $*" >&2; exit 1; }
[ -f "$TAR" ] || die "missing TAR: $TAR"
[ -f "$SHA_FILE" ] || die "missing SHA file: $SHA_FILE"
[ -f "$REC" ] || die "missing receipt: $REC"
[ -f "$PUB" ] || die "missing minisign pubkey: $PUB"

hash_tar(){
  if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | tr -d "\r" | cut -d" " -f1; return; fi
  if command -v certutil   >/dev/null 2>&1; then certutil -hashfile "$(cygpath -w "$1" 2>/dev/null || echo "$1")" SHA256 2>/dev/null | sed -n "2p" | tr -d " \r\n"; return; fi
  die "no sha256 tool found (need sha256sum or certutil)"
}

H1=$(hash_tar "$TAR")
H2=$(head -n1 "$SHA_FILE" | tr -d "\r" | cut -d" " -f1)
H3=$(sed -n "s/.*\"sha256\":\"\\([^\"]*\\)\".*/\\1/p" "$REC" | head -n1 | tr -d "\r")
[ -n "$H1" ] && [ -n "$H2" ] && [ -n "$H3" ] || die "empty hash encountered (H1=$H1 H2=$H2 H3=$H3)"
printf "%s\n" "$H1" | grep -Eq "^[A-Fa-f0-9]{64}$" || die "bad sha256 from tar: $H1"
printf "%s\n" "$H2" | grep -Eq "^[A-Fa-f0-9]{64}$" || die "bad sha256 in file: $H2"
[ "$H1" = "$H2" ] || die "sha mismatch against *.sha256 (tar=$H1 file=$H2)"
[ "$H1" = "$H3" ] || die "sha mismatch against receipt.json (tar=$H1 rec=$H3)"

minisign -Vm "$TAR" -p "$PUB" >/dev/null
echo "OK: sha256 matches (*.sha256 + receipt) and seller minisign verifies."
