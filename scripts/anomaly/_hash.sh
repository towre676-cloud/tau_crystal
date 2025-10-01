#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
hash_file(){
  fpath="$1"; [ -f "$fpath" ] || { echo "MISSING"; return 0; }
  tmp=".hash_tmp.$$"; trap 'rm -f "$tmp"' EXIT
  tr -d "\r" < "$fpath" > "$tmp" 2>/dev/null || cp -f "$fpath" "$tmp"
  if command -v sha256sum >/dev/null 2>&1; then sha256sum "$tmp" | awk "{print \$1}"; rm -f "$tmp"; trap - EXIT; return 0; fi
  if command -v shasum     >/dev/null 2>&1; then shasum -a 256 "$tmp" | awk "{print \$1}"; rm -f "$tmp"; trap - EXIT; return 0; fi
  if command -v openssl    >/dev/null 2>&1; then openssl dgst -sha256 "$tmp" | awk "{print \$NF}"; rm -f "$tmp"; trap - EXIT; return 0; fi
  if command -v certutil   >/dev/null 2>&1; then certutil -hashfile "$tmp" SHA256 | awk "NF && !/SHA256|hash of file|certutil/ {gsub(/\r/,\"\",$0); print \$0; exit}"; rm -f "$tmp"; trap - EXIT; return 0; fi
  size="$(wc -c < "$tmp" | tr -d "[:space:]")"; rm -f "$tmp"; trap - EXIT; echo "SIZE_${size}"
}
