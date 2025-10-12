#!/usr/bin/env bash
set +H; set -euo pipefail; umask 022; export LC_ALL=C
if [ "${1-}" = "" ] || [ "${2-}" = "" ] || [ "${3-}" = "" ]; then printf "usage: %s GEO ALPHA OUT_JSON\n" "$(basename "$0")" >&2; exit 64; fi
geo="$1"; alpha="$2"; out_json="$3"
work=".tau_ledger/work/${geo}/${alpha}"; mkdir -p "$work/raw"
NMAX="${NMAX:-120}"; RMAX="${RMAX:-6}"
TAU_GRID="${TAU_GRID:-i,0.5i,0.7745966692i,1.154700538i}"
Z_GRID="${Z_GRID:-0,1/6,1/3,1/2}"
./scripts/atlas/fiber_build.py --geo "$geo" --alpha "$alpha" --nmax "$NMAX" --rmax "$RMAX" --tau-grid "$TAU_GRID" --z-grid "$Z_GRID" --out "${work}/raw/fiber_raw.json"
spec="$("./scripts/atlas/spec_hash.sh")"
envh="$("./scripts/atlas/env_manifest.sh" .tau_ledger/spec/env.json)"
py="$(command -v python3 || command -v python)"
"$py" ./scripts/atlas/payload_hash.py "$work" "$work/_payload.json"
if command -v sha256sum >/dev/null 2>&1; then res=$(sha256sum "$work/_payload.json" | awk "{print \$1}"); else res=$(openssl dgst -sha256 -r "$work/_payload.json" | awk "{print \$1}"); fi
"$py" ./scripts/atlas/stack_pack.py --geo "$geo" --alpha "$alpha" --raw "${work}/raw" --spec-hash "$spec" --env-hash "$envh" --result-hash "$res" --out "$out_json"
