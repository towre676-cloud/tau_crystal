#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C

ROOT="${ROOT:-$(pwd)}"
OUTDIR="${OUTDIR:-.tau_ledger/corridor}"
TMPDIR="${TMPDIR:-.cache}"
LOCKDIR="$TMPDIR/.bind_corridor.lock"
NOW_UTC="$(date -u +%Y-%m-%dT%H:%M:%SZ || true)"
HOST="$(uname -a 2>/dev/null || echo unknown)"

sha256_of() {
  if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | awk "{print \$1}";
  else openssl dgst -sha256 "$1" | awk "{print \$2}"; fi
}
filesize_of() { wc -c < "$1" | tr -d "[:space:]\r"; }
mtime_of() {
  if stat -c %%Y "$1" >/dev/null 2>&1; then stat -c %%Y "$1";
  elif stat -f %%m "$1" >/dev/null 2>&1; then stat -f %%m "$1";
  else echo 0; fi
}
emit_json_string() { printf "%s" "$1" | sed -e 's/\\/\\\\/g' -e 's/"/\\"/g'; }

require_files=(
  ".tau_ledger/reflection/report.json"
  ".tau_ledger/cohomology/h1_obstruction.json"
  ".tau_ledger/lean_module_capsules/capsule_set.seal.json"
)

echo "[bind] corridor receipt..."
mkdir -p "$OUTDIR" "$TMPDIR"
if mkdir "$LOCKDIR" 2>/dev/null; then :; else echo "[busy] another bind in progress"; exit 75; fi
trap 'rmdir "$LOCKDIR" 2>/dev/null || true' EXIT
missing=0
for f in "${require_files[@]}"; do [ -s "$f" ] || { echo "[FAIL] missing or empty: $f"; missing=1; }; done
if [ "$missing" = 1 ]; then echo "[err] required inputs missing — corridor bind aborted"; exit 66; fi

diglist="$TMPDIR/.corridor_digests.$$"
inputs_json="$TMPDIR/.corridor_inputs.$$"
: > "$diglist"; : > "$inputs_json"
printf "%s" "[" >> "$inputs_json"
comma=""
for f in "${require_files[@]}"; do
  d="$(sha256_of "$f")"; s="$(filesize_of "$f")"; t="$(mtime_of "$f")"
  printf "%s\n" "$d" >> "$diglist"
  printf "%s" "$comma" >> "$inputs_json"
  printf "%s" "{" >> "$inputs_json"
  printf "%s" "\"path\":\"" >> "$inputs_json"
  emit_json_string "$f" >> "$inputs_json"
  printf "%s" "\"," >> "$inputs_json"
  printf "%s" "\"size\":$s," >> "$inputs_json"
  printf "%s" "\"mtime\":$t," >> "$inputs_json"
  printf "%s" "\"sha256\":\"$d\"}" >> "$inputs_json"
  comma=","
done
printf "%s" "]" >> "$inputs_json"

if command -v sha256sum >/dev/null 2>&1; then MRK="$(sha256sum "$diglist" | awk "{print \$1}")"; else MRK="$(openssl dgst -sha256 "$diglist" | awk "{print \$2}")"; fi
RID="corridor_$(date -u +%Y%m%dT%H%M%SZ)_$(echo "$MRK" | cut -c1-12)"
TMPJSON="$TMPDIR/$RID.tmp.json"; : > "$TMPJSON"
printf "%s" "{" >> "$TMPJSON"
printf "%s" "\"type\":\"tau_corridor_bind\"," >> "$TMPJSON"
printf "%s" "\"created_utc\":\"$NOW_UTC\"," >> "$TMPJSON"
printf "%s" "\"host\":\"" >> "$TMPJSON"; emit_json_string "$HOST" >> "$TMPJSON"; printf "%s" "\"," >> "$TMPJSON"
printf "%s" "\"inputs\":" >> "$TMPJSON"; cat "$inputs_json" >> "$TMPJSON"; printf "%s" "," >> "$TMPJSON"
printf "%s" "\"merkle_root\":\"$MRK\"" >> "$TMPJSON"
printf "%s" "}" >> "$TMPJSON"
OUT="$OUTDIR/$RID.json"; mv -f "$TMPJSON" "$OUT"
rm -f "$diglist" "$inputs_json" 2>/dev/null || true
echo "[ok] bound → $OUT"
