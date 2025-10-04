#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
if git rev-parse --is-inside-work-tree >/dev/null 2>&1; then ROOT="$(git rev-parse --show-toplevel 2>/dev/null || printf "%s" "$PWD")"; else ROOT="${ROOT_OVERRIDE:-$HOME/Desktop/tau_crystal/tau_crystal}"; fi
cd "$ROOT" || { echo "[error] could not cd to ROOT=$ROOT" >&2; exit 2; }
TARGET="${1:-}"; if [ -z "$TARGET" ]; then TARGET="$(ls -1t .tau_ledger/*/*/curvature/*.tsv 2>/dev/null | head -n 1 || true)"; fi
if [ -z "${TARGET:-}" ] || [ ! -f "$TARGET" ]; then echo "[gate:fail] no curvature TSV found"; exit 3; fi
rows="$(awk -F"\t" 'NR>1{c+=1} END{print (c+0)}' "$TARGET")"
if [ "${rows:-0}" -lt 1 ]; then echo "[gate:fail] zero data rows"; exit 4; fi
bad="$(awk -F"\t" 'NR>1{c++; for(i=1;i<=NF;i++){s[i]+=$i; ss[i]+=$i*$i}} END{ if(c==0){print 1; exit} for(i=1;i<=NF;i++){ m=s[i]/c; v=(ss[i]/c - m*m); if(v<0) v=0; if(m!=m || v!=v || m==1/0 || m==-1/0) {print 1; exit} } print 0 }' "$TARGET")"
if [ "${bad:-1}" -ne 0 ]; then echo "[gate:fail] non-finite stats"; exit 5; fi
echo "[gate:ok] curvature looks sane: rows=$rows file=$TARGET"
