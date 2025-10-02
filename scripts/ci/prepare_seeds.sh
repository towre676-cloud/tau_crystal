#!/usr/bin/env bash
set -euo pipefail
cap="${1:-}"; mkdir -p analysis

write_if_missing(){ p="$1"; s="$2"; [ -f "$p" ] || { mkdir -p "$(dirname "$p")"; printf "%s" "$s" > "$p"; }; }

if [ "$cap" = "affine_rg" ]; then
  write_if_missing analysis/affine_rg/a1_canon.json "{\"b\":1,\"mu0\":2,\"ell\":0.125,\"two_loop\":true,\"omega\":\"(dmu/mu^2 + b dℓ)\",\"reparam_scalar\":1}"
  write_if_missing analysis/affine_rg/a2_canon.json "{\"b\":2,\"mu0\":3,\"ell\":0.25,\"two_loop\":true,\"omega\":\"(dmu/mu^2 + b dℓ)\",\"reparam_scalar\":2}"
fi

if [ "$cap" = "modular" ]; then
  write_if_missing analysis/modular/mod_canon.json "{\"S\":[[0.7071067811865476,0.7071067811865476],[0.7071067811865476,-0.7071067811865476]],\"T\":[[[0.9659258262890683,-0.25881904510252074],0],[0,[0.25881904510252074,0.9659258262890683]]]}"
fi
