#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
out="${1:-.tau_ledger/phys/lattice.json}"
a="${A:-1.0}"; b="${B:-1.2}"; c="${C:-1.5}"
kx="${KX:-10.0}"; ky="${KY:-12.0}"; kz="${KZ:-14.0}"
m="${M:-1.0}"
ts=$(date -u +%Y-%m-%dT%H:%M:%SZ)
: > "$out"
printf "{\n" >> "$out"
printf "  \"schema\": \"taucrystal/lattice.v1\",\n" >> "$out"
printf "  \"timestamp\": \"%s\",\n" "$ts" >> "$out"
printf "  \"cell\": {\"type\": \"orthorhombic\", \"a\": %0.9f, \"b\": %0.9f, \"c\": %0.9f},\n" "$a" "$b" "$c" >> "$out"
printf "  \"mass\": %0.9f,\n" "$m" >> "$out"
printf "  \"force\": {\"kx\": %0.9f, \"ky\": %0.9f, \"kz\": %0.9f}\n" "$kx" "$ky" "$kz" >> "$out"
printf "}\n" >> "$out"
