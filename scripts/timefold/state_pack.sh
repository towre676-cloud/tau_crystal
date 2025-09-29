#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
sha(){ if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1"|awk "{print \$1}"; else openssl dgst -sha256 "$1"|awk "{print \$2}"; fi; }
sz(){ wc -c < "$1" | tr -d "[:space:]\r"; }
mt(){ stat -c %Y "$1" 2>/dev/null || stat -f %m "$1" 2>/dev/null || echo 0; }
now(){ date -u +%Y-%m-%dT%H:%M:%SZ || true; }
host(){ uname -a 2>/dev/null || echo unknown; }
CREF="${1:-}"
if [ -z "$CREF" ]; then CREF="$(ls -1t .tau_ledger/corridor/corridor_*.json 2>/dev/null | head -n1 || true)"; fi
[ -n "$CREF" ] || { echo "[err] no corridor receipt"; exit 66; }
[ -f "$CREF" ] || { echo "[err] corridor not found: $CREF"; exit 66; }
inputs=(
  ".tau_ledger/reflection/report.json"
  ".tau_ledger/cohomology/h1_obstruction.json"
  ".tau_ledger/lean_module_capsules/capsule_set.seal.json"
  ".tau_ledger/git/git_head.txt"
  ".tau_ledger/entropy/entropy_compare_20250929T050131Z_d56e9ce8a719.json"
  "$(ls -1t .tau_ledger/entropy/witness_*.json 2>/dev/null | head -n1)"
  "$CREF"
)
missing=0
for f in "${inputs[@]}"; do [ -s "$f" ] || { echo "[miss] $f"; missing=1; }; done
[ "$missing" = 0 ] || { echo "[err] missing inputs"; exit 66; }
CID="$(sha "$CREF" | cut -c1-12)"
RID="state_$(date -u +%Y%m%dT%H%M%SZ)_$CID"
LIST=".cache/$RID.files"; : > "$LIST"
for f in "${inputs[@]}"; do printf "%s\n" "$f" >> "$LIST"; done
TAR=".tau_ledger/timefold/state/$RID.tar"
GZ="$TAR.gz"
tar -cf "$TAR" --no-recursion -T "$LIST"
if command -v gzip >/dev/null 2>&1; then gzip -f "$TAR"; else mv -f "$TAR" "$TAR.tmp" && bsdtar -czf "$GZ" -T "$LIST" && rm -f "$TAR.tmp"; fi
TSHA="$(sha "$GZ")"
TMP=".cache/$RID.tmp.json"; : > "$TMP"
printf "%s" "{" >> "$TMP"
printf "%s" "\"type\":\"tau_timefold_state\"," >> "$TMP"
printf "%s" "\"created_utc\":\"$(now)\"," >> "$TMP"
printf "%s" "\"host\":\"$(host)\"," >> "$TMP"
printf "%s" "\"corridor_receipt\":\"" >> "$TMP"
printf "%s" "$CREF" >> "$TMP"
printf "%s" "\"," >> "$TMP"
printf "%s" "\"state_tar\":\"" >> "$TMP"
printf "%s" "$GZ" >> "$TMP"
printf "%s" "\"," >> "$TMP"
printf "%s" "\"state_sha\":\"" >> "$TMP"
printf "%s" "$TSHA" >> "$TMP"
printf "%s" "\"," >> "$TMP"
printf "%s" "\"inputs\":[" >> "$TMP"
comma=""
for f in "${inputs[@]}"; do
  printf "%s" "$comma" >> "$TMP"
  printf "%s" "{" >> "$TMP"
  printf "%s" "\"path\":\"" >> "$TMP"
  printf "%s" "$f" >> "$TMP"
  printf "%s" "\"," >> "$TMP"
  printf "%s" "\"size\":" >> "$TMP"
  printf "%s" "$(sz "$f")" >> "$TMP"
  printf "%s" "," >> "$TMP"
  printf "%s" "\"mtime\":" >> "$TMP"
  printf "%s" "$(mt "$f")" >> "$TMP"
  printf "%s" "," >> "$TMP"
  printf "%s" "\"sha256\":\"" >> "$TMP"
  printf "%s" "$(sha "$f")" >> "$TMP"
  printf "%s" "\"}" >> "$TMP"
  comma=","
done
printf "%s" "]" >> "$TMP"
printf "%s" "}" >> "$TMP"
OUT=".tau_ledger/timefold/state/$RID.json"
mv -f "$TMP" "$OUT"
echo "[ok] state -> $OUT"
MARK="timefold_mark_$(date -u +%Y%m%dT%H%M%SZ)_$CID"
MTMP=".cache/$MARK.tmp.json"; : > "$MTMP"
printf "%s" "{" >> "$MTMP"
printf "%s" "\"type\":\"tau_timefold_mark\"," >> "$MTMP"
printf "%s" "\"created_utc\":\"$(now)\"," >> "$MTMP"
printf "%s" "\"state_receipt\":\"" >> "$MTMP"
printf "%s" "$OUT" >> "$MTMP"
printf "%s" "\"," >> "$MTMP"
printf "%s" "\"state_tar\":\"" >> "$MTMP"
printf "%s" "$GZ" >> "$MTMP"
printf "%s" "\"," >> "$MTMP"
printf "%s" "\"state_sha\":\"" >> "$MTMP"
printf "%s" "$TSHA" >> "$MTMP"
printf "%s" "\"}" >> "$MTMP"
mv -f "$MTMP" ".tau_ledger/timefold/$MARK.json"
echo "[ok] mark -> .tau_ledger/timefold/$MARK.json"
