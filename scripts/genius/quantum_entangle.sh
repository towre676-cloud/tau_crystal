#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
. scripts/genius/_util.sh
n="${1:-2}"
root=".tau_ledger/genius"; mkdir -p "$root"
t=$(ts); hid=$(printf '%s\n' "$t-$RANDOM" | sha -)
p=$(pi)
for i in $(seq 1 "$n"); do
  ang=$(awk -v i="$i" -v p="$p" 'BEGIN{print i*(p/3)}')  # π/3 steps → sin^2 = 0.75 for i=1,2
  tau=$(sin2 "$ang")
  f="$root/entangle-$t-$i.meta"
  : > "$f"
  printf 'schema: %s\n' "taucrystal/entangle/v1" >> "$f"
  printf 'id: %s\n' "entangle-$t-$i" >> "$f"
  printf 'utc: %s\n' "$t" >> "$f"
  printf 'hidden: %s\n' "$hid" >> "$f"
  printf 'angle: %s\n' "$ang" >> "$f"
  printf 'tau: %s\n' "$tau" >> "$f"
done
echo "[OK] entangled: $n"
