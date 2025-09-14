#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
. scripts/genius/_util.sh
n="${1:-2}"
root=".tau_ledger/genius"; mkdir -p "$root"
t=$(ts); hid=$(printf '%s\n' "$t-$RANDOM" | sha -)
p=$(pi)
for i in $(seq 1 "$n"); do
  ang=$(awk -v i="$i" -v p="$p" 'BEGIN{print i*(p/2)}')
  tau=$(sin2 "$ang")
  f="$root/entangle-$t-$i.meta"
  : > "$f"
  emit_kv schema taucrystal/entangle/v1 "$f"
  emit_kv id "entangle-$t-$i" "$f"
  emit_kv utc "$t" "$f"
  emit_kv hidden "$hid" "$f"
  emit_kv angle "$ang" "$f"
  emit_kv tau "$tau" "$f"
done
echo "[OK] entangled: $n"
