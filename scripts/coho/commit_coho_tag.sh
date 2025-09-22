#!/usr/bin/env bash
set -Ee -o pipefail; set +H; umask 022
cd "$HOME/Desktop/tau_crystal/tau_crystal" || exit 1
[ -x scripts/coho/morphism_live.sh ] || { echo "::error::missing scripts/coho/morphism_live.sh"; exit 2; }
bash scripts/coho/morphism_live.sh .tau_ledger/last_run_A.json .tau_ledger/last_run_B.json || true
[ -f .tau_ledger/coho_obstructions.json ] || { echo "::error::no coho receipt produced"; exit 3; }
COHO=".tau_ledger/coho_obstructions.json"
H=$(sha256sum "$COHO" | awk "{print \\$1}")
TS=$(date -u +%Y-%m-%dT%H:%M:%SZ)
REC="corridor.receipt.tsv"; CHAIN=".tau_ledger/CHAIN"; touch "$REC" "$CHAIN"
grep -Fq "$H"$t"$COHO" "$REC" || printf "sha256:%s\t%s\n" "$H" "$COHO" >> "$REC"
grep -Fq "$H" "$CHAIN" || printf "%s\tcoho\tsha256:%s\t%s\n" "$TS" "$H" "$COHO" >> "$CHAIN"
jid(){ awk -F\" -v K="$2" '$1 ~ "^[[:space:]]*\""K"\"[[:space:]]*:[[:space:]]*\"" {print $4; exit}' "$1" 2>/dev/null; }
jnum(){ awk -v K="$2" '$0 ~ "^[[:space:]]*\""K"\"[[:space:]]*:" {gsub(/[^0-9-]/,"",$0); print $0; exit}' "$1" 2>/dev/null; }
AID=$(jid "$COHO" src_id); BID=$(jid "$COHO" dst_id)
AENV=$(jid "$COHO" src_env); BENV=$(jid "$COHO" dst_env)
OBS=$(jnum "$COHO" obstruction); : "${OBS:=0}"
PAIR="$AENV|$BENV"
PAIRH=$(printf "%s" "$PAIR" | sha256sum | awk "{print \\$1}")
LB=${PAIRH:62:2}
LBV=$(awk -v hx="$LB" 'BEGIN{print strtonum("0x"hx)}')
SECT=$(( LBV % 7 ))
SECTNAME="Frob_$SECT"
abs(){ n=$1; [ "$n" -lt 0 ] && echo $(( -n )) || echo "$n"; }
OBSABS=$(abs "$OBS")
mod(){ v=$1; m=$2; echo $(( v % m )); }
R2=$(mod "$OBSABS" 2); R3=$(mod "$OBSABS" 3); R5=$(mod "$OBSABS" 5); R7=$(mod "$OBSABS" 7); R11=$(mod "$OBSABS" 11)
TAG=".tau_ledger/coho_frobenius_tag.json"; : > "$TAG"
printf "{\n" >> "$TAG"
printf "  \\"coho_frobenius\\": {\n" >> "$TAG"
printf "    \\"timestamp\\": \\"%s\\",\n" "$TS" >> "$TAG"
printf "    \\"src\\": \\"%s\\",\n" "$AID" >> "$TAG"
printf "    \\"dst\\": \\"%s\\",\n" "$BID" >> "$TAG"
printf "    \\"env_pair\\": \\"%s\\",\n" "$PAIR" >> "$TAG"
printf "    \\"sector\\": \\"%s\\",\n" "$SECTNAME" >> "$TAG"
printf "    \\"obstruction\\": %s,\n" "$OBS" >> "$TAG"
printf "    \\"residue_mod\\": {\\"2\\": %s, \\"3\\": %s, \\"5\\": %s, \\"7\\": %s, \\"11\\": %s},\n" "$R2" "$R3" "$R5" "$R7" "$R11" >> "$TAG"
printf "    \\"hash\\": \\"sha256:%s\\"\n" "$H" >> "$TAG"
printf "  }\n}\n" >> "$TAG"
HT=$(sha256sum "$TAG" | awk "{print \\$1}")
grep -Fq "$HT"$t".tau_ledger/coho_frobenius_tag.json" "$REC" || printf "sha256:%s\t%s\n" "$HT" "$TAG" >> "$REC"
grep -Fq "$HT" "$CHAIN" || printf "%s\tfrobenius\tsha256:%s\t%s\n" "$TS" "$HT" "$TAG" >> "$CHAIN"
git add "$REC" "$CHAIN" "$COHO" "$TAG"
git commit -m "coho: corridor+CHAIN stamp and Frobenius sector tag; CACBE-safe writer"
git push origin main
