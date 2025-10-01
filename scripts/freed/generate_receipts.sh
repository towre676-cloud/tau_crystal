#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
ROOT="${1:-.}"; LED=".tau_ledger/freed"; mkdir -p "$LED"
stamp="$(date -u +%Y%m%dT%H%M%SZ)"
rf="$LED/relative_tft_receipt_$stamp.json"
af="$LED/anomaly_pullback_receipt_$stamp.json"
tf="$LED/tmf_sigma_receipt_$stamp.json"
: > "$rf"; printf "%s\n" "{" >> "$rf"; printf "%s\n" "  \"type\": \"relative_tft\", \"status\": \"pending\", \"note\": \"F_rel monoidality on generators and Čech H1=0 recorded here\", \"stamp\": \"$stamp\"" >> "$rf"; printf "%s\n" "}" >> "$rf"
: > "$af"; printf "%s\n" "{" >> "$af"; printf "%s\n" "  \"type\": \"anomaly_pullback\", \"status\": \"pending\", \"equation\": \"Phi_star(omega) = d log T_mot\", \"bridges\": [\"PF\",\"AGT\",\"SW\"], \"stamp\": \"$stamp\"" >> "$af"; printf "%s\n" "}" >> "$af"
: > "$tf"; printf "%s\n" "{" >> "$tf"; printf "%s\n" "  \"type\": \"tmf_sigma\", \"status\": \"pending\", \"invariant\": \"sigma‑orientation of q‑leg into tmf\", \"stamp\": \"$stamp\"" >> "$tf"; printf "%s\n" "}" >> "$tf"
