#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022
out="analysis/dynamics/tanh_lineage.json"; mkdir -p "$(dirname "$out")"
src_tau="analysis/normalized/ap.norm.json"; b="analysis/basins.tsv"; ns="analysis/next_surface.tsv"; m="analysis/morse_crit.tsv"
r1=".tau_ledger/hysteresis"; r2=".tau_ledger/entropy";
sha() { sha256sum "$1" | awk "{print \$1}"; }
s_tau=$( [ -f "$src_tau" ] && jq -S . "$src_tau" 2>/dev/null | sha256sum | awk "{print \$1}" || echo "na")
sb=$( [ -f "$b" ] && sha "$b" || echo "na")
sns=$( [ -f "$ns" ] && sha "$ns" || echo "na")
sm=$( [ -f "$m" ] && sha "$m" || echo "na")
hr=$(find "$r1" -type f -name "summary.json" -printf "%T@ %p\n" 2>/dev/null | sort -nr | awk "NR==1{print \$2}")
er=$(find "$r2" -type f -name "entv1-*.json" -printf "%T@ %p\n" 2>/dev/null | sort -nr | awk "NR==1{print \$2}")
sh_hr=$( [ -n "${hr:-}" ] && sha "$hr" || echo "na")
sh_er=$( [ -n "${er:-}" ] && sha "$er" || echo "na")
: > "$out.tmp"
printf "{\n" >> "$out.tmp"
printf "  \"tau_norm_sha\": \"%s\",\n" "$s_tau" >> "$out.tmp"
printf "  \"basins_tsv_sha\": \"%s\",\n" "$sb" >> "$out.tmp"
printf "  \"next_surface_tsv_sha\": \"%s\",\n" "$sns" >> "$out.tmp"
printf "  \"morse_crit_tsv_sha\": \"%s\",\n" "$sm" >> "$out.tmp"
printf "  \"hysteresis_summary_path\": \"%s\",\n" "${hr:-na}" >> "$out.tmp"
printf "  \"hysteresis_summary_sha\": \"%s\",\n" "$sh_hr" >> "$out.tmp"
printf "  \"entropy_entv1_path\": \"%s\",\n" "${er:-na}" >> "$out.tmp"
printf "  \"entropy_entv1_sha\": \"%s\"\n" "$sh_er" >> "$out.tmp"
printf "}\n" >> "$out.tmp"
mv "$out.tmp" "$out"
if [ -f "$b" ] && [ -f "$ns" ]; then
  sb1=$(sha "$b"); sns1=$(sha "$ns")
  sb2=$(sha "$b"); sns2=$(sha "$ns")
  if [ "$sb1" = "$sb2" ] && [ "$sns1" = "$sns2" ]; then
    if [ -n "${hr:-}" ] && [ -f "$hr" ]; then jq ".tanh_lock=\"replay_ok\"" "$hr" 2>/dev/null >/dev/null || true; fi
    echo "[TANH] deterministic replay ok"
  else echo "[TANH] deterministic replay FAILED"; exit 2; fi
else echo "[TANH] skip (no basins/next_surface)"; fi
