#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
NOTE1="${1:-}"; NOTE2="${2:-}"
[ -f "$NOTE1" ] || { echo "[err] missing first note path"; exit 2; }
[ -f "$NOTE2" ] || { echo "[err] missing second note path"; exit 2; }
LED="analysis/morpho/ledger/morpho_receipts.jsonl"
[ -s "$LED" ] || { echo "[err] no ledger at $LED"; exit 3; }
sha(){ openssl dgst -sha256 "$1" | awk "{print \$2}"; }
N1_SHA="$(sha "$NOTE1")"; N2_SHA="$(sha "$NOTE2")"
LAST=$(awk 'NF{line=$0} END{print line}' "$LED")
LED_N1=$(printf "%s" "$LAST" | grep -o "\"face_txt_sha256\":\"[^\"]*\"" 2>/dev/null | head -n1 | cut -d\" -f4)
LED_N2=$(printf "%s" "$LAST" | grep -o "\"face2_txt_sha256\":\"[^\"]*\"" 2>/dev/null | head -n1 | cut -d\" -f4)
echo "[verify] computed FACE.txt sha256 : $N1_SHA"
echo "[verify] computed face2.txt sha256: $N2_SHA"
if [ -n "$LED_N1" ]; then echo "[verify] ledger FACE.txt sha256  : $LED_N1"; else echo "[verify] ledger FACE.txt sha256  : <absent>"; fi
if [ -n "$LED_N2" ]; then echo "[verify] ledger face2.txt sha256 : $LED_N2"; else echo "[verify] ledger face2.txt sha256 : <absent>"; fi
OK1="MISMATCH"; OK2="MISMATCH"
[ -n "$LED_N1" ] && [ "$N1_SHA" = "$LED_N1" ] && OK1="MATCH"
[ -n "$LED_N2" ] && [ "$N2_SHA" = "$LED_N2" ] && OK2="MATCH"
echo "[status] FACE.txt  : $OK1"
echo "[status] face2.txt : $OK2"
echo "------------------ FACE.txt (verbatim) ------------------"
cat "$NOTE1"
echo ""
echo "------------------ face2.txt (verbatim) -----------------"
cat "$NOTE2"
echo ""
