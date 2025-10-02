#!/usr/bin/env bash
set -eu; set +H; umask 022; export LC_ALL=C LANG=C
cd "$(git rev-parse --show-toplevel 2>/dev/null || pwd)" || exit 1
hash_file(){ f="$1"; if command -v sha256sum >/dev/null 2>&1; then sha256sum "$f" 2>/dev/null | awk "{print \$1}";
elif command -v certutil >/dev/null 2>&1; then certutil -hashfile "$f" SHA256 2>/dev/null | sed -n "2p" | tr -d "\r "; else printf "%s" 0; fi; }
canon_hash=$( [ -f canon.json ] && hash_file canon.json || printf "%s" 0 )
status=".tau_ledger/corridor_status.json"; status_hash=$( [ -f "$status" ] && hash_file "$status" || printf "%s" 0 )
outdir=".tau_ledger/field"; mkdir -p "$outdir"; digest="$outdir/corridor.json"
: > "$digest"
printf "%s\n" "{" >> "$digest"
printf "%s\n" "  \"canon_hash\": \"$canon_hash\"," >> "$digest"
printf %sn "  \"status_hash\": \"$status_hash\"," >> "$TMP"
printf %sn printf
%s\n
  "timestamp": "2025-10-02T03:50:54Z"
printf "%s\n" "}" >> "$digest"
echo "[ok] wrote $digest"
