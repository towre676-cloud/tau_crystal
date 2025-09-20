#!/usr/bin/env bash
set +e; set +H; umask 022
cd "$HOME/Desktop/tau_crystal/tau_crystal" || { echo "cd failed"; :; }
TAB="$(printf '\t')"
_have(){ command -v "$1" >/dev/null 2>&1; }
_hash(){ if _have sha256sum; then sha256sum "$1" | awk '{print $1}'; elif _have openssl; then openssl dgst -sha256 "$1" | awk '{print $NF}'; else echo ""; fi; }
jstr(){ sed -n -E "s/^[[:space:]]*\"$2\"[[:space:]]*:[[:space:]]*\"([^\"]*)\".*/\1/p" "$1" | head -n1; }
jint(){ sed -n -E "s/^[[:space:]]*\"$2\"[[:space:]]*:[[:space:]]*([-]?[0-9]+).*/\1/p" "$1" | head -n1; }
if [ -d .tau_ledger/CHAIN ]; then
  [ -d .tau_ledger/CHAIN.d ] || mv .tau_ledger/CHAIN .tau_ledger/CHAIN.d
fi
touch .tau_ledger/CHAIN
A=".tau_ledger/last_run_A.json"; B=".tau_ledger/last_run_B.json"
if [ ! -f "$A" ] || [ ! -f "$B" ]; then
  ts=$(date -u +%Y%m%dT%H%M%SZ)
  aid="synthetic_A_$ts"; bid="synthetic_B_$ts"
  aenv="runner-A@toolchain-1"; benv="runner-B@toolchain-1"
  aroot=$(printf "%s" "$aid$aenv" | sha256sum | awk "{print \\$1}")
  broot=$(printf "%s" "$bid$benv" | sha256sum | awk "{print \\$1}")
  atau=42; btau=41
  : > "$A"; : > "$B"
  printf "{\n  \"id\": \"%s\",\n  \"root\": \"%s\",\n  \"env\": \"%s\",\n  \"tau\": %s\n}\n" "$aid" "$aroot" "$aenv" "$atau" >> "$A"
  printf "{\n  \"id\": \"%s\",\n  \"root\": \"%s\",\n  \"env\": \"%s\",\n  \"tau\": %s\n}\n" "$bid" "$broot" "$benv" "$btau" >> "$B"
fi
[ -x scripts/coho/morphism_live.sh ] || { echo "::warn::missing scripts/coho/morphism_live.sh"; exit 0; }
bash scripts/coho/morphism_live.sh "$A" "$B" || echo "::warn::morphism_live returned nonzero"
[ -f .tau_ledger/coho_obstructions.json ] || { echo "::warn::no coho receipt produced"; exit 0; }
REC="corridor.receipt.tsv"; touch "$REC"
COHO=".tau_ledger/coho_obstructions.json"; H=$(_hash "$COHO")
if [ -n "$H" ]; then
  line="sha256:$H${TAB}${COHO}"; grep -Fq "$line" "$REC" || printf "%s\n" "$line" >> "$REC"
  ts=$(date -u +%Y-%m-%dT%H:%M:%SZ); cline="${ts}${TAB}coho${TAB}sha256:${H}${TAB}${COHO}"
  grep -Fq "$H" .tau_ledger/CHAIN || printf "%s\n" "$cline" >> .tau_ledger/CHAIN
fi
AID=$(jstr "$COHO" src_id); BID=$(jstr "$COHO" dst_id)
AENV=$(jstr "$COHO" src_env); BENV=$(jstr "$COHO" dst_env)
OBS=$(jint "$COHO" obstruction); [ -n "$OBS" ] || OBS=0
PAIR="${AENV}|${BENV}"
PAIRF=".tau_ledger/.env_pair.txt"; printf "%s" "$PAIR" > "$PAIRF"
PH=$(_hash "$PAIRF"); [ -n "$PH" ] || PH=0000000000000000000000000000000000000000000000000000000000000000
LB="${PH:62:2}"; case "$LB" in [0-9a-fA-F][0-9a-fA-F]) :;; *) LB="00";; esac
LBV=$((16#$LB)); SECT=$((LBV % 7)); SECTNAME="Frob_${SECT}"
OBSABS=$(( OBS < 0 ? -OBS : OBS ))
R2=$(( OBSABS % 2 )); R3=$(( OBSABS % 3 )); R5=$(( OBSABS % 5 )); R7=$(( OBSABS % 7 )); R11=$(( OBSABS % 11 ))
TAG=".tau_ledger/coho_frobenius_tag.json"; : > "$TAG"
printf "{\n" >> "$TAG"
printf "  \\"coho_frobenius\\": {\n" >> "$TAG"
printf "    \\"timestamp\\": \\"%s\\",\n" "$(date -u +%Y-%m-%dT%H:%M:%SZ)" >> "$TAG"
printf "    \\"src\\": \\"%s\\",\n" "$AID" >> "$TAG"
printf "    \\"dst\\": \\"%s\\",\n" "$BID" >> "$TAG"
printf "    \\"env_pair\\": \\"%s\\",\n" "$PAIR" >> "$TAG"
printf "    \\"sector\\": \\"%s\\",\n" "$SECTNAME" >> "$TAG"
printf "    \\"obstruction\\": %s,\n" "$OBS" >> "$TAG"
printf "    \\"residue_mod\\": {\\"2\\": %s, \\"3\\": %s, \\"5\\": %s, \\"7\\": %s, \\"11\\": %s},\n" "$R2" "$R3" "$R5" "$R7" "$R11" >> "$TAG"
printf "    \\"hash\\": \\"sha256:%s\\"\n" "$H" >> "$TAG"
printf "  }\n}\n" >> "$TAG"
HT=$(_hash "$TAG")
if [ -n "$HT" ]; then
  tline="sha256:$HT${TAB}${TAG}"; grep -Fq "$tline" "$REC" || printf "%s\n" "$tline" >> "$REC"
  tcline="$(date -u +%Y-%m-%dT%H:%M:%SZ)${TAB}frobenius${TAB}sha256:${HT}${TAB}${TAG}"
  grep -Fq "$HT" .tau_ledger/CHAIN || printf "%s\n" "$tcline" >> .tau_ledger/CHAIN
fi
git add "$REC" .tau_ledger/CHAIN "$TAG" "$COHO" scripts/coho/fix_and_tag.sh >/dev/null 2>&1 || : 
git commit -m "coho: repair CHAIN file, synthesize A/B if missing, emit coho receipt + Frobenius tag" >/dev/null 2>&1 || : 
git push origin main >/dev/null 2>&1 || : 
echo "fix_and_tag: completed (soft-errors tolerated), shell preserved."
