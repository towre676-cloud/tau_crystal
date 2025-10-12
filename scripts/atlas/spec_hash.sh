#!/usr/bin/env bash
set +H; set -euo pipefail; umask 022; export LC_ALL=C
sha() { if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | awk "{print \$1}"; else openssl dgst -sha256 -r "$1" | awk "{print \$1}"; fi; }
files=(
  scripts/atlas/fiber_build.py
  scripts/atlas/stack_pack.py
  scripts/atlas/make_fiber.sh
  scripts/atlas/build_stack.sh
)
tmp=".tau_ledger/spec/_list.txt"; : > "$tmp"
for f in "${files[@]}"; do [ -f "$f" ] || { printf "missing:%s\n" "$f" >> "$tmp"; continue; }; printf "%s:%s\n" "$f" "$(sha "$f")" >> "$tmp"; done
sort "$tmp" -o "$tmp"
if command -v sha256sum >/dev/null 2>&1; then root=$(sha256sum "$tmp" | awk "{print \$1}"); else root=$(openssl dgst -sha256 -r "$tmp" | awk "{print \$1}"); fi
printf "%s\n" "$root" > .tau_ledger/spec/spec_hash.txt
printf "%s\n" "$root"
