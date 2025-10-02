#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
latest_json="";
for f in analysis/reflection/run_*/report.json; do [ -f "$f" ] || continue; if [ -z "${latest_json-}" ] || [ "$f" -nt "$latest_json" ]; then latest_json="$f"; fi; done
[ -n "${latest_json-}" ] || { echo "[REFLECT] no report.json found"; exit 66; }
flat="$(tr -d "\r\n\t " < "$latest_json" 2>/dev/null || printf "")"
noq="${flat//\"/}"
fix=""; case "$noq" in *fixpoint:true*) fix=true ;; *fixpoint:false*) fix=false ;; esac
if [ -z "${fix-}" ]; then
  spec=false; tailok=false; resok=false
  case "$noq" in *spectral:true*) spec=true ;; esac
  case "$noq" in *tail:true*) tailok=true ;; esac
  resnum="$(printf "%s" "$noq" | sed -n "s/.*obstruction_residue:\\([0-9][0-9]*\\.[0-9][0-9]*\\).*/\\1/p" | head -n1 2>/dev/null || printf "")"
  if [ -n "${resnum-}" ]; then awk -v r="$resnum" "BEGIN{exit !(r<0.020)}"; [ "$?" -eq 0 ] && resok=true || resok=false; fi
  if [ "$spec" = true ] && [ "$tailok" = true ] && [ "$resok" = true ]; then fix=true; else fix=false; fi
fi
echo "[REFLECT] $(dirname "$latest_json" | xargs basename) fixpoint=${fix-unknown}"
[ "${fix-false}" = true ] || { echo "[REFLECT] stability not reached"; exit 65; }
