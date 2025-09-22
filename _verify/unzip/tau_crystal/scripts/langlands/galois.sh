#!/usr/bin/env bash
set -Eeuo pipefail; set +H
STATE=".galois/automorphisms.tsv"; mkdir -p .galois
gen(){
  places="linux x86 windows mingw macos arm64 docker baremetal"
  : > "$STATE"; for r in 0 1 2 3 4 5 6 7; do
    m=(); i=0; for p in $places; do m[$i]="$p"; i=$((i+1)); done
    # rotate r
    for ((k=0;k<${#m[@]};k++)); do from="${m[$k]}"; to="${m[$(( (k+r)%${#m[@]} ))]}"; printf "sigma_%d\t%s\t%s\n" "$r" "$from" "$to" >> "$STATE"; done
  done; echo "[ok] wrote $STATE"
}
show(){ [ -f "$STATE" ] && cat "$STATE" || echo "[err] none; run: galois.sh gen" ; }
case "${1:-}" in gen) gen;; show) show;; *) echo "usage: galois.sh gen|show" >&2; exit 2;; esac
