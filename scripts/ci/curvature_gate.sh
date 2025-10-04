#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
if git rev-parse --is-inside-work-tree >/dev/null 2>&1; then ROOT="$(git rev-parse --show-toplevel 2>/dev/null || printf "%s" "$PWD")"; else ROOT="${ROOT_OVERRIDE:-$HOME/Desktop/tau_crystal/tau_crystal}"; fi
cd "$ROOT" || { echo "[gate:error] cannot cd to ROOT=$ROOT" >&2; exit 2; }
TARGET="${1:-}"
if [ -z "$TARGET" ]; then
  # Prefer tracked curvature files (stable on CI), newest first
  TARGET="$(git ls-files -z ".tau_ledger/*/*/curvature/*.tsv" 2>/dev/null | tr -d "\0" | xargs -r -I{} bash -lc 'printf "%s\t%010d\n" "{}" "$(test -f "{}" && perl -e "printf((stat shift)[9])" "{}" || echo 0)' | sort -k2,2nr | awk 'NR==1{print $1}' || true)"
  if [ -z "$TARGET" ]; then
    TARGET="$(find .tau_ledger -type f -path "*/curvature/*.tsv" -printf "%T@ %p\n" 2>/dev/null | sort -nr | awk '{sub(/^[^ ]+ /,""); print; exit}' || true)"
  fi
fi
if [ -z "${TARGET:-}" ] || [ ! -f "$TARGET" ]; then echo "[gate:fail] no curvature TSV found"; exit 3; fi
# Strip CR for MSYS safety into a temp
tmp="$(mktemp "${TMPDIR:-/tmp}/curv.XXXXXX.tsv")"; trap 'rm -f "$tmp"' EXIT
tr -d "\r" < "$TARGET" > "$tmp" || { echo "[gate:error] unable to sanitize $TARGET" >&2; exit 6; }
# Count data rows (skip header)
rows="$(awk -F"\t" 'NR>1{c+=1} END{print (c+0)}' "$tmp")"
if [ "${rows:-0}" -lt 1 ]; then echo "[gate:fail] zero data rows in $TARGET"; exit 4; fi
# Compute means/stds and detect non-finite
bad="$(awk -F"\t" 'NR>1{c++; for(i=1;i<=NF;i++){x=$i+0; s[i]+=x; ss[i]+=x*x}} END{ if(c<1){print 1; exit} for(i=1;i<=NF;i++){ m=s[i]/c; v=(ss[i]/c - m*m); if(v<0) v=0; if(m!=m || v!=v || m==1/0 || m==-1/0) {print 1; exit} } print 0 }' "$tmp")"
if [ "${bad:-1}" -ne 0 ]; then echo "[gate:fail] non-finite stats in $TARGET"; exit 5; fi
echo "[gate:ok] rows=$rows file=$TARGET"
