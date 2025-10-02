#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
out="${1:-.tau_ledger/morpho/global.L}"; shift || true
[ "$#" -ge 1 ] || { echo "usage: l_series_compose.sh OUT LOCAL1 [LOCAL2 ...]" >&2; exit 2; }
mkdir -p "$(dirname "$out")"
sumH=0; n=0; c1=0; c2=0; c3=0
for f in "$@"; do [ -f "$f" ] || continue; H=$(awk -F= "\$1==\"H\"{print \$2}" "$f"); EV=$(awk -F= "\$1==\"EVEN\"{print \$2}" "$f"); OD=$(awk -F= "\$1==\"ODD\"{print \$2}" "$f");
  sumH=$(awk -v a="$sumH" -v b="${H:-0}" "BEGIN{printf \"%.8f\", a+b}")
  c1=$(awk -v a="$c1" -v b="${EV:-0}" "BEGIN{printf \"%.8f\", a+b}")
  c2=$(awk -v a="$c2" -v b="${OD:-0}" "BEGIN{printf \"%.8f\", a+b}")
  z=$(awk -v e="${EV:-0}" -v o="${OD:-0}" "BEGIN{t=e+o; if(t==0)print 0; else printf \"%.8f\", (e-o)/t}")
  c3=$(awk -v a="$c3" -v b="$z" "BEGIN{printf \"%.8f\", a+b}")
  n=$((n+1))
done
[ "$n" -gt 0 ] || { echo "no locals" >&2; exit 3; }
Hbar=$(awk -v s="$sumH" -v n="$n" "BEGIN{printf \"%.8f\", s/n}")
ts=$(date -u +%Y%m%dT%H%M%SZ)
: > "$out"
printf "%s\n" "N=$n"         >> "$out"
printf "%s\n" "H_BAR=$Hbar"  >> "$out"
printf "%s\n" "C1=$c1"       >> "$out"
printf "%s\n" "C2=$c2"       >> "$out"
printf "%s\n" "C3=$c3"       >> "$out"
printf "%s\n" "TIME=%s" "$ts" >> "$out"
echo "ok: L-like composed -> $out (H_BAR=$Hbar, N=$n)"
