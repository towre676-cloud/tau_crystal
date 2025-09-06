#!/usr/bin/env bash
set -euo pipefail
mkdir -p out

commit="$(git rev-parse HEAD 2>/dev/null || echo "unknown")"
ts="$(date -u +"%Y-%m-%dT%H:%M:%SZ" || echo "unknown")"
seed="${TAU_SEED:-42}"

# --- Demo transcript (portable ints/floats) ---
if [ "$seed" = "42" ]; then
  tau='[0.1,0.2,0.3]'
  rk='[7,13,19]'
else
  tau='[0.1,0.25,0.31]'
  rk='[7,11,19]'
fi

# --- Step hash-chain (Hi = sha256(Hi-1 || event)) ---
H="0000000000000000000000000000000000000000000000000000000000000000"
events=()
# Flatten tau + rk as events
events+=($(echo "$tau" | tr -d '[]' | tr ',' ' '))
events+=($(echo "$rk"  | tr -d '[]' | tr ',' ' '))
for ev in "${events[@]}"; do
  H=$(printf '%s|%s' "$H" "$ev" | sha256sum | awk '{print $1}')
done
ticks="${#events[@]}"

# --- Hardware sealing (best-effort) ---
gpu_vendor="unknown"; gpu_model=""; gpu_driver=""; gpu_uuid=""
opaque='[]'
if command -v nvidia-smi >/dev/null 2>&1; then
  gpu_vendor="nvidia"
  gpu_model="$(nvidia-smi --query-gpu=name --format=csv,noheader 2>/dev/null | head -n1 || true)"
  gpu_driver="$(nvidia-smi --query-gpu=driver_version --format=csv,noheader 2>/dev/null | head -n1 || true)"
  gpu_uuid="$(nvidia-smi --query-gpu=gpu_uuid --format=csv,noheader 2>/dev/null | head -n1 || true)"
  # Seal detailed report digest as an opaque byteproof
  if nvidia-smi -x -q > out/nvidia-smi.xml 2>/dev/null; then
    dh="$(sha256sum out/nvidia-smi.xml | awk '{print $1}')"
    opaque="[ {\"kind\":\"nvidia-smi.xml\",\"sha256\":\"$dh\"} ]"
  fi
elif command -v rocm-smi >/dev/null 2>&1; then
  gpu_vendor="amd"
  gpu_model="$(rocm-smi --showproductname 2>/dev/null | awk -F': ' '/Product Name/{print $2; exit}' || true)"
  gpu_driver="$(rocm-smi --showdriverversion 2>/dev/null | awk -F': ' '/Driver version/{print $2; exit}' || true)"
fi

# --- Toolchain pin (best-effort) ---
lean_ver=""
[ -f lean-toolchain ] && lean_ver="$(tr -d '\r' < lean-toolchain | head -n1)"
std_rev="$(git -C .lake/packages/std rev-parse HEAD 2>/dev/null || echo "")"

# --- Freeze ambient context (zip digest) ---
ctx_json="$(./scripts/tau-freeze.sh)"
ctx_sha=""
ctx_size=0
ctx_path=""
if [ -f out/context.json ]; then
  ctx_path="$(grep -o '"path": *"[^"]*"' out/context.json | sed -E 's/.*"([^"]+)"/\1/')"
  if [ -n "$ctx_path" ] && [ -f "$ctx_path" ]; then
    ctx_sha="$(sha256sum "$ctx_path" | awk '{print $1}')"
    ctx_size="$(wc -c <"$ctx_path")"
  fi
fi

# --- Build manifest ---
cat > out/manifest.json <<JSON
{
  "kind": "tau-crystal-receipt",
  "version": "1",
  "component": "fusion",
  "commit_hash": "$commit",
  "timestamp_utc": "$ts",

  "equivalence_level": "portable",
  "clock": { "scheme": "step+syscall", "ticks": $ticks, "hash_chain": "$H" },

  "hardware": { "gpu": { "vendor":"$gpu_vendor","model":"$gpu_model","driver":"$gpu_driver","uuid":"$gpu_uuid" } },
  "opaque": $opaque,

  "toolchain": { "lean": { "channel": "$lean_ver" }, "std4": { "rev": "$std_rev" } },

  "tau_series": $tau,
  "rank_kernel": $rk,

  "context": {
    "scheme": "tau-freeze/1",
    "archive_path": "$ctx_path",
    "sha256": "$ctx_sha",
    "size": $ctx_size
  }
}
JSON

sha256sum out/manifest.json | awk '{print $1 " *out/manifest.json"}' > out/manifest.json.sha256
echo "✅ wrote out/manifest.json"
echo "   sha256: $(cut -d' ' -f1 out/manifest.json.sha256)"
