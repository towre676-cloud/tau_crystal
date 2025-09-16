#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
cd "$(dirname "$0")/../.." || exit 1

EPS="${PHYSICS_EPS:-1e-6}"
OUT_CP="analysis/cp_residual.tsv"
OUT_PP="analysis/passport_sig.tsv"
OUT_FUSED="analysis/fused_gates.json"

# 1) run CP residual (non-exiting to always collect receipts)
set +e
OUT="$OUT_CP" EPS="$EPS" bash scripts/tools/cp_residual_symm_verifier.sh analysis/morse_crit.tsv 1 3
cp_rc=$?
set -e

# extract CP fields
cp_residual=$(awk -F"\t" '$1=="residual"{print $2}' "$OUT_CP" 2>/dev/null || echo NaN)
cp_epsilon=$(awk  -F"\t" '$1=="epsilon"{print  $2}' "$OUT_CP" 2>/dev/null || echo "$EPS")
cp_pass=$(awk     -F"\t" '$1=="pass"{print     $2}' "$OUT_CP" 2>/dev/null || echo 0)

# 2) run passport probe (non-exiting to always collect receipts)
set +e
OUT="$OUT_PP" bash scripts/physics/passport_probe.sh
pp_rc=$?
set -e

# extract passport fields
pp_nonce=$(awk -F"\t" '$1=="nonce_hex"{print $2}' "$OUT_PP" 2>/dev/null || echo "")
pp_sig=$(awk   -F"\t" '$1=="sig_hex"{print   $2}' "$OUT_PP" 2>/dev/null || echo "")
pp_pub=$(awk   -F"\t" '$1=="pub_hex"{print   $2}' "$OUT_PP" 2>/dev/null || echo "")
pp_pass=$(awk  -F"\t" '$1=="pass"{print      $2}' "$OUT_PP" 2>/dev/null || echo 0)

# 3) fused flag (string-safe: treat any non-1 as failure)
fused_pass=0
[ "$cp_pass" = "1" ] && [ "$pp_pass" = "1" ] && fused_pass=1

# optional chain timestamp source (last entry first column), else empty
ts=""
[ -s ".tau_ledger/chain/CHAIN" ] && ts=$(tail -n1 .tau_ledger/chain/CHAIN | awk -F"\t" '{print $1}' | tr -d "\r\n") || true

# 4) emit deterministic JSON with fixed key order (no jq, no Python)
: > "$OUT_FUSED"
printf "%s" "{" >> "$OUT_FUSED"
printf "%s" "\"schema\":\"taucrystal/physics_fused_gates/v1\"" >> "$OUT_FUSED"
printf "%s" ",\"ts\":\"$ts\"" >> "$OUT_FUSED"
printf "%s" ",\"cp_residual\":{" >> "$OUT_FUSED"
printf "%s" "\"residual\":$cp_residual" >> "$OUT_FUSED"
printf "%s" ",\"epsilon\":$cp_epsilon" >> "$OUT_FUSED"
printf "%s" ",\"pass\":$( [ "$cp_pass" = "1" ] && echo true || echo false )" >> "$OUT_FUSED"
printf "%s" "}" >> "$OUT_FUSED"
printf "%s" ",\"passport\":{" >> "$OUT_FUSED"
printf "%s" "\"nonce\":\"$pp_nonce\"" >> "$OUT_FUSED"
printf "%s" ",\"sig\":\"$pp_sig\"" >> "$OUT_FUSED"
printf "%s" ",\"pk\":\"$pp_pub\"" >> "$OUT_FUSED"
printf "%s" ",\"pass\":$( [ "$pp_pass" = "1" ] && echo true || echo false )" >> "$OUT_FUSED"
printf "%s" "}" >> "$OUT_FUSED"
printf "%s" ",\"fused_pass\":$( [ "$fused_pass" = "1" ] && echo true || echo false )" >> "$OUT_FUSED"
printf "%s\n" "}" >> "$OUT_FUSED"

# 5) stamp sha256 and append to chain
shahex=""
if command -v sha256sum >/dev/null 2>&1; then shahex=$(sha256sum "$OUT_FUSED" | cut -d" " -f1);
elif command -v shasum >/dev/null 2>&1; then shahex=$(shasum -a 256 "$OUT_FUSED" | cut -d" " -f1);
else shahex=$(openssl dgst -sha256 "$OUT_FUSED" | awk '{print $NF}'); fi
printf "%s  %s\n" "$shahex" "$OUT_FUSED" > "${OUT_FUSED}.sha256"
stamp=$(date -u +%Y-%m-%dT%H:%M:%SZ)
printf "%s\t%s\t%s\n" "$stamp" "$OUT_FUSED" "$shahex" >> .tau_ledger/chain/CHAIN

# 6) final exit code
[ "$fused_pass" = "1" ] && exit 0 || exit 8
