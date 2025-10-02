#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
sha() {
  if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | awk "{print \$1}";
  else openssl dgst -sha256 "$1" | awk "{print \$2}"; fi
}
now() { date -u +%Y-%m-%dT%H:%M:%SZ || true; }
host() { uname -a 2>/dev/null || echo unknown; }
SRC="${1:-.tau_ledger/corridor}"
last="$(ls -1t "$SRC"/corridor_*.json 2>/dev/null | head -n1 || true)"
[ -n "$last" ] || { echo "[err] no corridor receipt"; exit 66; }
CID="$(sha "$last" | cut -c1-12)"
RID="timefold_mark_$(date -u +%Y%m%dT%H%M%SZ)_$CID"
TMP=".cache/$RID.tmp.json"
: > "$TMP"
printf "%s" "{" >> "$TMP"
printf "%s" "\"type\":\"tau_timefold_mark\"," >> "$TMP"
printf "%s" "\"created_utc\":\"$(now)\"," >> "$TMP"
printf "%s" "\"host\":\"$(host)\"," >> "$TMP"
printf "%s" "\"corridor_receipt\":\"$last\"," >> "$TMP"
printf "%s" "\"corridor_sha\":\"$(sha "$last")\"" >> "$TMP"
printf "%s" "}" >> "$TMP"
OUT=".tau_ledger/timefold/$RID.json"
mv -f "$TMP" "$OUT"
echo "[ok] mark -> $OUT"
