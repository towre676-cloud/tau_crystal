#!/usr/bin/env bash
set -euo pipefail

mkdir -p out

commit="$(git rev-parse HEAD)"
ts="$(date -u +"%Y-%m-%dT%H:%M:%SZ")"
seed="${TAU_SEED:-42}"

# --- Demo transcript (portable) ---
if [ "$seed" = "42" ]; then
  tau='[0.1,0.2,0.3]'
  rk='[7,13,19]'
else
  tau='[0.1,0.25,0.31]'
  rk='[7,11,19]'
fi

# --- Minimal hash chain over events (tau + rk) ---
H="0000000000000000000000000000000000000000000000000000000000000000"
upd(){ H="$(printf "%s%s" "$H" "$1" | sha256sum | awk '{print $1}')"; }
for v in 0.1 0.2 0.3; do upd "tau:$v"; done
for v in 7 13 19; do upd "rk:$v"; done
if [ "$seed" != "42" ]; then
  H="0000000000000000000000000000000000000000000000000000000000000000"
  for v in 0.1 0.25 0.31; do upd "tau:$v"; done
  for v in 7 11 19; do upd "rk:$v"; done
fi
ticks=6

# --- Toolchain info (Lean) ---
lean_path="$(command -v lean || echo "")"
lean_ver=""; lean_sha=""
if [ -n "$lean_path" ]; then
  lean_ver="$(lean --version 2>/dev/null | head -n1 | awk '{print $NF}')"
  lean_sha="$(sha256sum "$lean_path" | awk '{print $1}')"
fi

# std4 rev (best-effort)
std_rev="unknown"
if [ -f lake-manifest.json ]; then
  cand="$(grep -oE '"std4".*"rev"[^"]*"[^"]*' lake-manifest.json | tail -n1 | sed -E 's/.*"rev"[[:space:]]*:[[:space:]]*"([^"]*)/\1/')"
  [ -n "$cand" ] && std_rev="$cand"
fi

# --- GPU info (best-effort) ---
gpu_vendor="unknown"; gpu_model=""; gpu_driver=""; gpu_uuid=""
if command -v nvidia-smi >/dev/null 2>&1; then
  IFS=',' read -r gpu_model gpu_driver gpu_uuid < <(nvidia-smi --query-gpu=name,driver_version,uuid --format=csv,noheader 2>/dev/null | head -n1)
  gpu_model="$(echo "$gpu_model" | xargs || true)"
  gpu_driver="$(echo "$gpu_driver" | xargs || true)"
  gpu_uuid="$(echo "$gpu_uuid" | xargs || true)"
  [ -n "$gpu_model" ] && gpu_vendor="nvidia"
else
  psout="$(powershell.exe -NoProfile -Command "\$g = Get-CimInstance Win32_VideoController | Select-Object -First 1 Name,DriverVersion; Write-Output \$g.Name; Write-Output \$g.DriverVersion" 2>/dev/null | tr -d '\r')"
  gpu_model="$(echo "$psout" | sed -n '1p')"
  gpu_driver="$(echo "$psout" | sed -n '2p')"
  if echo "$gpu_model" | grep -iq nvidia; then gpu_vendor="nvidia"; fi
fi

# Opaque driver digest (Windows CUDA driver DLL if present)
opaque_json="[]"
dll="/c/Windows/System32/nvcuda.dll"
if [ -f "$dll" ]; then
  dll_sha="$(sha256sum "$dll" | awk '{print $1}')"
  winp="$(cygpath -w "$dll" 2>/dev/null || echo "$dll")"
  winp_esc="${winp//\\/\\\\}"
  opaque_json="$(cat <<J
[
  {"kind":"driver","path":"$winp_esc","sha256":"$dll_sha"}
]
J
)"
fi

# --- Write JSON ---
cat > out/manifest.json <<JSON
{
  "kind": "tau-crystal-receipt",
  "version": "1",
  "component": "fusion",
  "commit_hash": "$commit",
  "timestamp_utc": "$ts",
  "tau_series": $tau,
  "rank_kernel": $rk,
  "equivalence_level": "portable",
  "clock": { "scheme": "step", "ticks": $ticks, "hash_chain": "$H" },
  "hardware": { "gpu": {
    "vendor": "$gpu_vendor",
    "model": "${gpu_model//\"/\\\"}",
    "driver": { "version": "${gpu_driver//\"/\\\"}" },
    "uuid": "${gpu_uuid//\"/\\\"}"
  }},
  "opaque": $opaque_json,
  "toolchain": {
    "lean": { "version": "${lean_ver:-}", "sha256": "${lean_sha:-}", "path": "${lean_path//\"/\\\"}" },
    "std4": { "rev": "$std_rev" }
  }
}
JSON

echo "wrote out/manifest.json (seed=$seed)"
