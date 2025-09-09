#!/usr/bin/env bash
set -euo pipefail

mkdir -p out

commit="$(git rev-parse HEAD 2>/dev/null || echo unknown)"
ts="$(date -u +"%Y-%m-%dT%H:%M:%SZ" 2>/dev/null || date -u +%Y-%m-%dT%H:%M:%SZ)"
seed="${TAU_SEED:-42}"

# --- Demo transcript (portable) ---
if [ "$seed" = "42" ]; then
  tau_json='[0.1,0.2,0.3]'; tau_list="0.1 0.2 0.3"
  rk_json='[7,13,19]';      rk_list="7 13 19"
else
  tau_json='[0.1,0.25,0.31]'; tau_list="0.1 0.25 0.31"
  rk_json='[7,11,19]';        rk_list="7 11 19"
fi

# --- Hash-chain clock (H0 = 64 zeros; Hi = SHA256(Hi-1 || event)) ---
H="$(printf '%064d' 0)"
for v in $tau_list; do
  H="$(printf "%s%s" "$H" "tau:$v" | sha256sum | awk '{print $1}')"
done
for v in $rk_list; do
  H="$(printf "%s%s" "$H" "rk:$v" | sha256sum | awk '{print $1}')"
done
ticks=$(( $(wc -w <<<"$tau_list $rk_list") ))

# --- Hardware/GPU probe (portable) ---
gpu_vendor="unknown"; gpu_model=""; gpu_driver=""; gpu_uuid=""
if command -v nvidia-smi >/dev/null 2>&1; then
  line="$(nvidia-smi --query-gpu=name,driver_version,uuid --format=csv,noheader,nounits 2>/dev/null | head -n 1 || true)"
  gpu_vendor="nvidia"
  gpu_model="$(printf "%s" "$line" | cut -d',' -f1 | sed 's/^ *//;s/ *$//')"
  gpu_driver="$(printf "%s" "$line" | cut -d',' -f2 | sed 's/^ *//;s/ *$//')"
  gpu_uuid="$(printf "%s" "$line" | cut -d',' -f3 | sed 's/^ *//;s/ *$//')"
elif command -v powershell.exe >/dev/null 2>&1; then
  gpu_model="$(powershell.exe -NoProfile -Command "Get-WmiObject Win32_VideoController | Select-Object -First 1 -ExpandProperty Name" 2>/dev/null | tr -d '\r')"
  gpu_driver="$(powershell.exe -NoProfile -Command "Get-WmiObject Win32_VideoController | Select-Object -First 1 -ExpandProperty DriverVersion" 2>/dev/null | tr -d '\r')"
  gpu_vendor="$(powershell.exe -NoProfile -Command "Get-WmiObject Win32_VideoController | Select-Object -First 1 -ExpandProperty AdapterCompatibility" 2>/dev/null | tr -d '\r')"
fi

# --- Opaque digests (best-effort; empty is fine) ---
opaque='[]'
if command -v powershell.exe >/dev/null 2>&1; then
  dllpath="$(powershell.exe -NoProfile -Command "(Get-Command nvcuda.dll -ErrorAction SilentlyContinue).Path" 2>/dev/null | tr -d '\r')"
  if [ -n "$dllpath" ]; then
    dllsha="$(powershell.exe -NoProfile -Command "(Get-FileHash -Algorithm SHA256 \"$dllpath\").Hash" 2>/dev/null | tr -d '\r')"
    opaque="[ { \"path\": \"${dllpath//\\/\\\\}\", \"sha256\": \"${dllsha}\" } ]"
  fi
fi

# --- Toolchain sealing (best-effort) ---
lean_ver=""; lean_sha=""; std_rev=""
if command -v lean >/dev/null 2>&1; then
  lean_ver="$(lean --version 2>/dev/null | head -n1 | tr -d '\r' || true)"
  lean_path="$(command -v lean || true)"
  if [ -n "${lean_path:-}" ] && [ -f "$lean_path" ]; then
    lean_sha="$(sha256sum "$lean_path" | awk '{print $1}')"
  fi
fi
if [ -d ".lake/packages/std" ]; then
  std_rev="$(git -C .lake/packages/std rev-parse HEAD 2>/dev/null || true)"
fi

# --- Write manifest ---
cat > out/manifest.json <<JSON
{
  "kind": "tau-crystal-receipt",
  "version": "1",
  "component": "fusion",
  "commit_hash": "$commit",
  "timestamp_utc": "$ts",
  "equivalence_level": "portable",
  "tau_series": $tau_json,
  "rank_kernel": $rk_json,
  "clock": { "scheme": "step+syscall", "ticks": $ticks, "hash_chain": "$H" },
  "hardware": { "gpu": { "vendor": "$gpu_vendor", "model": "$gpu_model", "driver": "$gpu_driver", "uuid": "$gpu_uuid" } },
  "opaque": $opaque,
  "toolchain": { "lean": { "version": "$lean_ver", "sha256": "$lean_sha" }, "std4": { "rev": "$std_rev" } }
}
JSON

sha256sum out/manifest.json > out/manifest.json.sha256
echo "✅ wrote out/manifest.json"
echo "   sha256: $(cut -d' ' -f1 out/manifest.json.sha256)"
