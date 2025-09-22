#!/usr/bin/env bash
set +e; set +H; umask 022
DL=".tau_ledger/delta.tsv"
SL=".tau_ledger/src_leaf.tsv"
DLF=".tau_ledger/dst_leaf.tsv"
MP=".tau_ledger/morphism_map.tsv"
TC=".tau_ledger/tau_cert.tsv"
OUT=".tau_ledger/delta_report.md"
[ -f "$DL" ] || { echo "::error::missing $DL"; :; }
L1=$(awk '{v=$2; if(v<0)v=-v; s+=v} END{print s+0}' "$DL")
SUP=$(awk '$2!=0{n++} END{print n+0}' "$DL")
POS=$(awk '$2>0{p++} END{print p+0}' "$DL")
NEG=$(awk '$2<0{q++} END{print q+0}' "$DL")
SRCN=$(awk '{s[$2]=1} END{print length(s)+0}' "$SL")
DSTN=$(awk '{d[$2]=1} END{print length(d)+0}' "$DLF")
MAT=$(awk '{m[$1]=$2} END{print length(m)+0}' "$MP" 2>/dev/null)
TAUS=$(awk '$1=="tau_src"{print $2}' "$TC" 2>/dev/null)
TAUD=$(awk '$1=="tau_dst"{print $2}' "$TC" 2>/dev/null)
TDR=$(awk '$1=="tau_drift_abs"{print $2}' "$TC" 2>/dev/null)
LBD=$(awk '$1=="lambda"{print $2}' "$TC" 2>/dev/null)
: > "$OUT"
printf "# Cohomology delta report (v2)\n\n" >> "$OUT"
printf "• ||Δ||_1: %s\n" "$L1" >> "$OUT"
printf "• support: %s (pos=%s, neg=%s)\n" "$SUP" "$POS" "$NEG" >> "$OUT"
printf "• leaves: src=%s, dst=%s, mapped=%s\n" "$SRCN" "$DSTN" "$MAT" >> "$OUT"
if [ -n "$TAUS$TAUD$TDR$LBD" ]; then printf "• tau_src=%s, tau_dst=%s, |Δtau|=%s, lambda=%s\n" "$TAUS" "$TAUD" "$TDR" "$LBD" >> "$OUT"; fi
printf "\n## Top 50 nonzero Δ entries by |coeff|\n\n" >> "$OUT"
awk '{a=$2; if(a<0)a=-a; print a"\t"$0}' "$DL" | sort -nr -k1,1 | head -n 50 | cut -f2- | awk 'BEGIN{print "| leaf_id | coeff |"; print "|---|---:|"} {printf "| %s | %s |\n",$1,$2}' >> "$OUT"
echo "$OUT"
