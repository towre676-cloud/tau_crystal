#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
cd "$(dirname "$0")/../.." || exit 1
OUT="analysis/hecke.tsv"
src=""; for f in analysis/qexpansion.tsv analysis/qexp.tsv analysis/coeffs.tsv; do [ -s "$f" ] && src="$f" && break; done
[ -z "$src" ] && { echo "[hecke] no q-expansion TSV found"; exit 2; }
awk -F"\t" 'function isprime(n,  i,lim){if(n<2)return 0;if(n%2==0)return n==2;lim=int(sqrt(n)+1);for(i=3;i<=lim;i+=2)if(n%i==0)return 0;return 1} NR==1 && ($1 ~ /n($|[^0-9])/i || $2 ~ /a_?n/i){next} {n=$1+0; a=$2+0; if(isprime(n)) print n "\t" a}' "$src" > "$OUT"
echo "[hecke] wrote $(wc -l < "$OUT") rows from $src → $OUT"
