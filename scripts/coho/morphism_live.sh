#!/usr/bin/env bash
set -Ee -o pipefail; set +H; umask 022
A=${1:-.tau_ledger/last_run_A.json}
B=${2:-.tau_ledger/last_run_B.json}
[ -f "$A" ] && [ -f "$B" ] || { echo "::error::missing $A or $B"; exit 2; }
jstr(){ awk -F\" -v K="$2" '$1 ~ "\"^\\s*\""K"\"\\s*:\\s*\"" {print $4; exit}' "$1" 2>/dev/null || true; }
jint(){ awk -v K="$2" '$0 ~ "^[[:space:]]*\""K"\"[[:space:]]*:" {gsub(/[^0-9-]/,"",$0); print $0; exit}' "$1" 2>/dev/null || true; }
hex_hamm(){
  local a=$(printf "%s" "$1" | tr "A-Z" "a-z"); local b=$(printf "%s" "$2" | tr "A-Z" "a-z")
  [ ${#a} -eq ${#b} ] || { echo 9999; return; }
  local i=0 d=0; while [ $i -lt ${#a} ]; do [ "${a:$i:1}" != "${b:$i:1}" ] && d=$((d+1)); i=$((i+1)); done; echo $d
}
aid=$(jstr "$A" id); aroot=$(jstr "$A" root); aenv=$(jstr "$A" env); atau=$(jint "$A" tau)
bid=$(jstr "$B" id); broot=$(jstr "$B" root); benv=$(jstr "$B" env); btau=$(jint "$B" tau)
: "${atau:=0}"; : "${btau:=0}"
msens=$(hex_hamm "$aroot" "$broot")
tdrift=$((atau - btau))
alpha=1; beta=1; abstd=$((tdrift<0?-tdrift:tdrift))
obstruction=$(( alpha*msens + beta*abstd ))
ts=$(date -u +%%Y-%%m-%%dT%%H:%%M:%%SZ)
OUT=".tau_ledger/coho_obstructions.json"
: > "$OUT"
printf "{\n" >> "$OUT"
printf "  \x22cohomology\x22: {\n" >> "$OUT"
printf "    \x22src_id\x22: \x22%s\x22,\n" "$aid" >> "$OUT"
printf "    \x22dst_id\x22: \x22%s\x22,\n" "$bid" >> "$OUT"
printf "    \x22src_root\x22: \x22%s\x22,\n" "$aroot" >> "$OUT"
printf "    \x22dst_root\x22: \x22%s\x22,\n" "$broot" >> "$OUT"
printf "    \x22src_env\x22: \x22%s\x22,\n" "$aenv" >> "$OUT"
printf "    \x22dst_env\x22: \x22%s\x22,\n" "$benv" >> "$OUT"
printf "    \x22tau_src\x22: %s,\n" "$atau" >> "$OUT"
printf "    \x22tau_dst\x22: %s,\n" "$btau" >> "$OUT"
printf "    \x22merkle_sensitivity_hex_hamming\x22: %s,\n" "$msens" >> "$OUT"
printf "    \x22tau_drift_abs\x22: %s,\n" "$abstd" >> "$OUT"
printf "    \x22alpha\x22: %s,\n" "$alpha" >> "$OUT"
printf "    \x22beta\x22: %s,\n" "$beta" >> "$OUT"
printf "    \x22obstruction\x22: %s,\n" "$obstruction" >> "$OUT"
printf "    \x22timestamp\x22: \x22%s\x22\n" "$ts" >> "$OUT"
printf "  }\n}\n" >> "$OUT"
echo "cohomology: wrote $OUT (obs=$obstruction, msens=$msens, |Δτ|=$abstd)"
