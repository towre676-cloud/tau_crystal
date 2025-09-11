#!/usr/bin/env bash
set -Eeuo pipefail
set +H
umask 022

sha256_file(){
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum "$1" | awk "{print \$1}"
  else
    openssl dgst -sha256 "$1" | awk "{print \$2}"
  fi
}

MONO="docs/MONOGRAPH.md"
[ -s "$MONO" ] || { echo "[err] missing $MONO"; exit 2; }
MR=$(sha256_file "$MONO")
TS=$(date -u +%Y-%m-%dT%H:%M:%SZ)
MAN=".tau_ledger/manifest.demo.json"
: > "$MAN"
printf %s "{\"producer\":\"tau-crystal 1.2.0\",\"timestamp\":\"$TS\",\"merkle_root\":\"$MR\"}" >> "$MAN"

RID="demo-$(date -u +%Y%m%dT%H%M%SZ)"
REC=".tau_ledger/receipts/$RID.json"
: > "$REC"
printf %s "{\"reflective\":{\"merkle_root\":\"$MR\"}}" >> "$REC"

CHASH=$(sha256_file "$REC")
CH=".tau_ledger/chain.head"
printf "%s %s\n" "$CHASH" "$REC" > "$CH"
echo "[ok] demo receipt built; chain -> $(tail -n1 "$CH")"
