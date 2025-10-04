#!/usr/bin/env bash
set -e; set -o pipefail; set +H; umask 022; export LC_ALL=C LANG=C
chain="${1:-.tau_ledger/CHAIN}"
k_req="${2:-4}"
out="${3:-artifacts/site/cover_cocycles.tsv}"
tmp="$(mktemp)"; trap 'rm -f "$tmp"' EXIT
mkdir -p "$(dirname "$out")" || :
if [ ! -f "$chain" ]; then echo "[err] CHAIN not found: $chain" >&2; exit 2; fi

mapfile -t H < <(awk "{print \$1}" "$chain")
n=${#H[@]}
printf "i\tj\tk\tcijk_len\n" > "$tmp"

ed(){ a="$1"; b="$2"; al=${#a}; bl=${#b}; m=$al; [ $bl -lt $m ] && m=$bl; s=0
      for i in $(seq 1 $m); do ca=${a:i-1:1}; cb=${b:i-1:1}; [ "$ca" = "$cb" ] || s=$((s+1)); done
      # count tail difference
      t=$(( (al>bl)? al-bl : bl-al )); echo $((s+t)); }

# choose k = min(k_req, n), but need at least 3 for triples
if [ "$n" -lt 3 ]; then
  # degrade: emit one dummy row with zeros for visibility
  printf "1\t1\t1\t0\n" >> "$tmp"
else
  k=$k_req; [ "$k" -gt "$n" ] && k="$n"
  for i in $(seq 1 "$k"); do
    for j in $(seq $((i+1)) "$k"); do
      for r in $(seq $((j+1)) "$k"); do
        h1="${H[i-1]}"; h2="${H[j-1]}"; h3="${H[r-1]}"
        l1=$(ed "$h1" "$h2"); l2=$(ed "$h2" "$h3"); l3=$(ed "$h3" "$h1")
        c=$(( (l1 + l2 + l3) % 997 ))
        printf "%d\t%d\t%d\t%d\n" "$i" "$j" "$r" "$c" >> "$tmp"
      done
    done
  done
fi

mv "$tmp" "$out"
echo "[ok] timefold cover cocycles -> $out"
