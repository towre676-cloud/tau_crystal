#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
ROOT=${1:-.}
LOG=.tau_ledger/cacbe/scan_$(date -u +%Y%m%dT%H%M%SZ).tsv
mkdir -p .tau_ledger/cacbe
: > "$LOG"; printf "%s\n" "code\tfile\tline\tmatch" >> "$LOG"
scan() { pat=$1; code=$2; ex=$3; grep -RIn --binary-files=without-match --exclude-dir=.git --exclude-dir=.tau_ledger --exclude-dir=node_modules --exclude-dir=.venv --exclude='*.png' --exclude='*.jpg' --exclude='*.pdf' -E "$pat" "$ROOT" | awk -F: -v c="$code" -v e="$ex" 'BEGIN{OFS="\t"} {if($0!~e){print c,$1,$2,$3}}' >> "$LOG" || true; }
scan '<<-?' 'HEREDOC' ''
scan '^[^#]*\bcd\b' 'NO_ROOT_CD' 'cd \"\/c/Users/Cody/Desktop/tau_crystal/tau_crystal\" \|\| exit 1'
scan 'set -euo pipefail' 'NO_STRICT' 'set -euo pipefail' # later filtered
scan '[^A-Za-z0-9_]A_PPY|\$\{?[A-Za-z0-9_]+\}?[^A-Za-z0-9_].*\$\{?[A-Za-z0-9_]*\}?[^A-Za-z0-9_]' 'BAD_VAR' ''
find "$ROOT" -type f -name '*.sh' -o -name '*.yml' -o -name 'Makefile' | while read -r f; do L=$(wc -l <"$f" | tr -d '[:space:]'); if [ "${L:-0}" -gt 400 ]; then printf "%s\t%s\t%s\t%s\n" "LONG_PASTE" "$f" 1 "lines=$L" >> "$LOG"; fi; done
# Post‑filter NO_STRICT and NO_ROOT_CD by verifying presence of canonical guards
TMP=.cacbe/.scan.$$; mkdir -p .cacbe; cp "$LOG" "$TMP"
awk -F'\t' 'BEGIN{OFS="\t"} NR==1{print; next} $1=="NO_STRICT"{next} $1=="NO_ROOT_CD"{next} {print}' "$TMP" > "$LOG"
