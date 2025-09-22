#!/usr/bin/env bash
set -Ee -o pipefail; set +H; umask 022
A=${1:-.tau_ledger/last_run_A.json}
B=${2:-.tau_ledger/last_run_B.json}
mkdir -p .tau_ledger
if [ ! -f "$A" ] || [ ! -f "$B" ]; then
  echo "::error::missing input transcripts $A or $B"; exit 2
fi
aid=$(awk -F\" \x27/\x5E\\s*\"id\"\\s*:\\s*\"/{print $4; exit}\x27 "$A" || true)
aroot=$(awk -F\" \x27/\x5E\\s*\"root\"\\s*:\\s*\"/{print $4; exit}\x27 "$A" || true)
aenv=$(awk -F\" \x27/\x5E\\s*\"env\"\\s*:\\s*\"/{print $4; exit}\x27 "$A" || true)
atau=$(awk -F: \x27/\x5E\\s*\"tau\"\\s*:\\s*/{gsub(/[, ]/,"",$2); print $2; exit}\x27 "$A" || echo 0)
bid=$(awk -F\" \x27/\x5E\\s*\"id\"\\s*:\\s*\"/{print $4; exit}\x27 "$B" || true)
broot=$(awk -F\" \x27/\x5E\\s*\"root\"\\s*:\\s*\"/{print $4; exit}\x27 "$B" || true)
benv=$(awk -F\" \x27/\x5E\\s*\"env\"\\s*:\\s*\"/{print $4; exit}\x27 "$B" || true)
btau=$(awk -F: \x27/\x5E\\s*\"tau\"\\s*:\\s*/{gsub(/[, ]/,"",$2); print $2; exit}\x27 "$B" || echo 0)
dst="$bid"; src="$aid"
sigmaEnv="${aenv}->${benv}"
tauDrift=$(( ${atau:-0} - ${btau:-0} ))
obs=$tauDrift
if [ "$dst" != "$bid" ] || [ "$src" != "$aid" ]; then obs=$((obs+1)); fi
if [ "$benv" != "$aenv" ]; then obs=$((obs+2)); fi
ts=$(date -u +%%Y-%%m-%%dT%%H:%%M:%%SZ)
OUT=".tau_ledger/coho_obstructions.json"
: > "$OUT"
printf "{\n" >> "$OUT"
printf "  \x22cohomology\x22: {\n" >> "$OUT"
printf "    \x22src_id\x22: \x22%s\x22,\n" "$aid" >> "$OUT"
printf "    \x22dst_id\x22: \x22%s\x22,\n" "$bid" >> "$OUT"
printf "    \x22sigma_env\x22: \x22%s\x22,\n" "$sigmaEnv" >> "$OUT"
printf "    \x22tau_drift\x22: %s,\n" "$tauDrift" >> "$OUT"
printf "    \x22obstruction\x22: %s,\n" "$obs" >> "$OUT"
printf "    \x22timestamp\x22: \x22%s\x22\n" "$ts" >> "$OUT"
printf "  }\n" >> "$OUT"
printf "}\n" >> "$OUT"
echo "cohomology: wrote $OUT (obstruction=$obs)"
