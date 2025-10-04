#!/usr/bin/env bash
set -e; set -o pipefail; set +H; umask 022; export LC_ALL=C LANG=C
lines="${1:-20}"
show(){ f="$1"; [ -f "$f" ] || { printf "\n--- %s (missing) ---\n" "$f"; return; }; printf "\n--- %s (tail -n %s) ---\n" "$f" "$lines"; tail -n "$lines" "$f" || true; }
show ".tau_ledger/CHAIN"
show "artifacts/remaining33.status.tsv"
show "artifacts/entropy/tau_entropy.tsv"
show "artifacts/hecke/hecke_classes.tsv"
show "artifacts/residue/zeta_residue.tsv"
show "artifacts/site/cover_cocycles.tsv"
show "artifacts/site/cup_product.tsv"
show "artifacts/site/obstruction.tsv"
show "artifacts/motivic/motivic_witness.tsv"
