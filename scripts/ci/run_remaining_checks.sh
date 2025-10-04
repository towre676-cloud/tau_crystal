#!/usr/bin/env bash
set -e; set -o pipefail; set +H; umask 022; export LC_ALL=C LANG=C
log="artifacts/remaining33.status.tsv"; tmp="$(mktemp)"; trap 'rm -f "$tmp"' EXIT
mkdir -p artifacts/motivic artifacts/hecke artifacts/residue artifacts/site artifacts/entropy || :
printf "component\tstatus\tdetail\n" > "$tmp"
if scripts/arith/motivic_lift.sh receipts/runs/descent_lean.synthetic_theta.json artifacts/motivic/motivic_witness.tsv 2>/dev/null; then [ -s artifacts/motivic/motivic_witness.tsv ] && printf "motivic_lift\tOK\twitness\n" >> "$tmp" || printf "motivic_lift\tFAIL\tno_witness\n" >> "$tmp"; else printf "motivic_lift\tFAIL\trun_error\n" >> "$tmp"; fi
if [ -f .tau_ledger/CHAIN ] && scripts/guards/hecke_classify.sh .tau_ledger/CHAIN 61 artifacts/hecke/hecke_classes.tsv 2>/dev/null; then [ -s artifacts/hecke/hecke_classes.tsv ] && printf "hecke_classify\tOK\tclasses\n" >> "$tmp" || printf "hecke_classify\tFAIL\tno_classes\n" >> "$tmp"; else printf "hecke_classify\tFAIL\tno_chain_or_error\n" >> "$tmp"; fi
