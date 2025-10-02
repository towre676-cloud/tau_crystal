#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
# Simulated bootstrap: deterministically expand seed -> blob -> compare hash
seed="bootstrap/seed.mu"; blob="bootstrap/stage0.xz"; led=".tau_ledger/bootstrap"
mkdir -p bootstrap "$led"
[ -s "$seed" ] || printf "%s\n" "MUPRELUDE=42;MAIN=\"tau\"" > "$seed"
rebuild="bootstrap/stage0.rebuild.xz"
tmp="bootstrap/_stage0.build"; : > "$tmp"
tr -d "\r" < "$seed" | sha256sum | awk "{print \$1}" > "$tmp"
printf "%s\n" "CRYSTALIZE" >> "$tmp"
xz -zc "$tmp" > "$rebuild"
[ -s "$blob" ] || cp -f "$rebuild" "$blob"
a=$(sha256sum "$blob" | awk "{print \$1}")
b=$(sha256sum "$rebuild" | awk "{print \$1}")
ts=$(date -u +"%Y-%m-%dT%H:%M:%SZ")
rec="$led/$ts.tsv"; : > "$rec"
printf "%s\t%s\n" "ts" "$ts" >> "$rec"
printf "%s\t%s\n" "seed_sha256" "$(sha256sum "$seed" | awk "{print \$1}")" >> "$rec"
printf "%s\t%s\n" "blob_sha256" "$a" >> "$rec"
printf "%s\t%s\n" "rebuild_sha256" "$b" >> "$rec"
if [ "$a" != "$b" ]; then echo "[ouroboros] mismatch"; exit 1; fi
echo "[ouroboros] ok $a"
