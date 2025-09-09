#!/usr/bin/env bash
set -euo pipefail
set +H
OUT="${1:-.tau_ledger/runner_fingerprint.json}"
command -v jq >/dev/null 2>&1 || { echo "[err] jq required"; exit 2; }
os_rel="$( (cat /etc/os-release 2>/dev/null || true) | tr -d "\r" )"
kern="$(uname -srmo 2>/dev/null || true)"
glibc="$( (ldd --version 2>/dev/null || true) | head -n1 | tr -s " " )"
img="${ImageVersion:-}${ImageOS:+ /}${ImageOS:-}"
lean_v="$( (lean --version 2>/dev/null || true) | tr -s " " )"
lake_v="$( (lake --version 2>/dev/null || true) | tr -s " " )"
elan_v="$( (~/.elan/bin/elan --version 2>/dev/null || elan --version 2>/dev/null || true) | tr -s " " )"
tool="$( (cat lean-toolchain 2>/dev/null || true) | tr -d "\r" )"
sha(){ command -v sha256sum >/dev/null 2>&1 && sha256sum "$1" | awk "{print \$1}" || echo ""; }
lean_p="$(command -v lean || true)"; lake_p="$(command -v lake || true)"; elan_p="$(command -v elan || true)"
jq -n --arg os "$os_rel" --arg kern "$kern" --arg glibc "$glibc" --arg img "$img" \
      --arg lean "$lean_v" --arg lake "$lake_v" --arg elan "$elan_v" --arg tool "$tool" \
      --arg lean_p "$lean_p" --arg lake_p "$lake_p" --arg elan_p "$elan_p" \
      --arg lean_sha "$( [ -n "$lean_p" ] && sha "$lean_p" )" \
      --arg lake_sha "$( [ -n "$lake_p" ] && sha "$lake_p" )" \
      --arg elan_sha "$( [ -n "$elan_p" ] && sha "$elan_p" )" \
      '{os_release:$os,kernel:$kern,glibc:$glibc,image:$img,lean:$lean,lake:$lake,elan:$elan,lean_toolchain:$tool,bin_sha:{lean:$lean_sha,lake:$lake_sha,elan:$elan_sha},bin_path:{lean:$lean_p,lake:$lake_p,elan:$elan_p}}' >"$OUT"
