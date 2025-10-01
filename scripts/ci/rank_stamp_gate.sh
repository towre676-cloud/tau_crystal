#!/usr/bin/env bash
set -Ee -o pipefail; set +H; umask 022
AT="analysis/atlas.jsonl"; [ -s "$AT" ] || { echo "[rank] no atlas; nothing to gate"; exit 0; }
LINE=$(tac "$AT" | awk '/\"type\":\"RANK_STAMP\"/{print; exit}')
[ -n "$LINE" ] || { echo "[rank] no RANK_STAMP found"; exit 0; }
Z=$(printf "%s" "$LINE" | sed -E 's/.*"zero_hash":"([a-f0-9]{64})".*/\1/')
R=$(printf "%s" "$LINE" | sed -E 's/.*"rank_hash":"([a-f0-9]{64})".*/\1/')
ZP=$(printf "%s" "$LINE" | sed -E 's/.*"zero_path":"([^"]+)".*/\1/')
RP=$(printf "%s" "$LINE" | sed -E 's/.*"rank_path":"([^"]+)".*/\1/')
[ "$Z" != "$R" ] || { echo "[rank] zero_hash == rank_hash (not independent)"; exit 20; }
[ -n "$ZP" ] && [ -n "$RP" ] || { echo "[rank] missing zero_path or rank_path"; exit 21; }
[ "$ZP" != "$RP" ] || { echo "[rank] identical codepaths"; exit 22; }
case "$ZP-$RP" in
  *scripts/langlands/hecke*scripts/langlands/hecke*) echo "[rank] both paths appear Hecke-derived"; exit 23;;
esac
echo "[rank] independence OK"
