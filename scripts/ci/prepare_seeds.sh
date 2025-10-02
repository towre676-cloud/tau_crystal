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
if [ "$cap" = "specnet" ]; then
  write_if_missing analysis/specnet/sn_pre_canon.json  "{\"charges\":[{\"gamma\":\"a\",\"Omega\":1},{\"gamma\":\"b\",\"Omega\":-1}]}"
  write_if_missing analysis/specnet/sn_post_canon.json "{\"charges\":[{\"gamma\":\"b\",\"Omega\":-1},{\"gamma\":\"a\",\"Omega\":1}]}"
fi
if [ "$cap" = "chamber" ]; then
  write_if_missing analysis/chamber/ch_ok_canon.json  "{\"rho\":[3,1,2,5,4],\"perm\":[0,1,2,3,4],\"sigma\":[1,2,3,4,5]}"
  write_if_missing analysis/chamber/ch_bad_canon.json "{\"rho\":[1,1,2,3,4],\"perm\":[0,1,2,3,4],\"sigma\":[1,1,2,3,4],\"should_fail\":true}"
fi
if [ "$cap" = "padic" ]; then
  write_if_missing analysis/padic/p_hQ_canon.json "{\"h_num\":3,\"h_den\":7,\"p\":5}"
  write_if_missing analysis/padic/p_hp_canon.json "{\"h_num\":3,\"h_den\":7,\"p\":5}"
fi
if [ "$cap" = "sset" ]; then
  write_if_missing analysis/sset/sset_horn_ok_canon.json  "{\"d0\":[0,1],\"d1\":[1,2],\"d2\":[0,2],\"filler\":true}"
  write_if_missing analysis/sset/sset_horn_bad_canon.json "{\"d0\":[0,1],\"d1\":[1,2],\"d2\":[0,2]}"
fi
if [ "$cap" = "anomaly" ]; then
  write_if_missing analysis/anomaly/anomaly_M1_canon.json         "{\"h\":3,\"T\":13}"
  write_if_missing analysis/anomaly/anomaly_M2_canon.json         "{\"h\":5,\"T\":13}"
  write_if_missing analysis/anomaly/anomaly_glued_canon.json      "{\"h\":2,\"T\":13}"
  write_if_missing analysis/anomaly/anomaly_glued_bad_canon.json  "{\"h\":1,\"T\":13}"
fi
