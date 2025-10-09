#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
ROOT="${ROOT_OVERRIDE:-$HOME/Desktop/tau_crystal/tau_crystal}"
cd "$ROOT" || { echo "[err] cd fail"; exit 2; }

y="${1:-0.7}"; N="${2:-60}"
# z from y = exp(2π i z)
z="$(python3 - <<'PY'
import sys, cmath
y=float(sys.argv[1]); print(cmath.log(y)/(2j*cmath.pi))
PY
"$y")"

printf "[quintic:q0] Ell|_{q^0} ~ -y^{-1} + 101  =>  "
python3 - <<'PY'
import sys; y=float(sys.argv[1]); print(f"{-1.0/y + 101.0:.10f}")
PY
"$y"

out="./tmp/ell_quintic_push.tsv"; : > "$out"
printf "#Re(tau)\tIm(tau)\tRe(z)\tIm(z)\tEll_r\tEll_i\n" >> "$out"

for TRe in 0.2 0.3 0.4; do
  for TIm in 0.6 0.7 0.8; do
    tau="${TRe}+${TIm}j"
    read er ei < <(python3 scripts/ell/ell_quintic_pushforward.py "$z" "$tau" "$N")
    zr="$(echo "$z" | sed 's/[() ]//g' | cut -d'+' -f1)"
    zi="$(echo "$z" | sed 's/[() ]//g' | sed 's/.*+//')"
    printf "%s\t%s\t%s\t%s\t%.9e\t%.9e\n" "$TRe" "$TIm" "$zr" "$zi" "$er" "$ei" >> "$out"
  done
done
echo "[push] wrote $out"
sed -n '1,5p' "$out"
