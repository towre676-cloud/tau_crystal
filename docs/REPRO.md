# Repro guide (bash-only)

## 1) Re-run a contract

```bash
# Example: TM1 sum-rule pre-gate
bash scripts/tau_exec.sh request.tm1_sumrule.json > analysis/tm1_sumrule.receipt.json
sed -n '1,120p' analysis/tm1_sumrule.receipt.json
```

## 2) Verify `input_sha256` (contract) and `request_sha256` (dispatch)

```bash
# Paths
REC="analysis/tm1_sumrule.receipt.json"
CONTRACT="$(jq -r '.contract_path // empty' "$REC" 2>/dev/null || true)"
[ -n "$CONTRACT" ] || CONTRACT="contracts/cp_residual_symm.tm1.contract.json"  # fallback if not embedded

# Hash contract (sha256sum or openssl)
if command -v sha256sum >/dev/null 2>&1; then
  H_CONTRACT="$(sha256sum "$CONTRACT" | awk '{print $1}')"
else
  H_CONTRACT="$(openssl dgst -sha256 "$CONTRACT" | awk '{print $2}')"
fi

# Extract fields without jq fallback
extract_json_key(){ grep -o '"'"$1"'"[[:space:]]*:[[:space:]]*"[^"]*"' "$REC" | head -n1 | sed -E 's/.*:"([^"]*)".*/\1/'; }

if command -v jq >/dev/null 2>&1; then
  H_IN_REC="$(jq -r '.input_sha256'  "$REC")"
  H_REQ_REC="$(jq -r '.request_sha256' "$REC")"
else
  H_IN_REC="$(extract_json_key input_sha256)"
  H_REQ_REC="$(extract_json_key request_sha256)"
fi

echo "contract sha256: $H_CONTRACT"
echo "receipt input_sha256: $H_IN_REC"
echo "receipt request_sha256: $H_REQ_REC"
[ "$H_CONTRACT" = "$H_IN_REC" ] && echo "[OK] contract hash matches receipt" || echo "[FAIL] mismatch"
```

## 3) Inspect latest campaign

```bash
camp="$(ls -d campaigns/residuals_*Z 2>/dev/null | tail -n1)"
sed -n '1,80p' "$camp/README.md"
sed -n '1,80p' "$camp/summary.json"
```

### Canonical hash verification (matches tool behavior)

```bash
CONTRACT="$(jq -r \".contract_path // empty\" analysis/tm1_sumrule.receipt.json 2>/dev/null || true)"; [ -n \"$CONTRACT\" ] || CONTRACT="contracts/cp_residual_symm.tm1.contract.json"
H_CANON="$(scripts/bin/json_sha256.sh "$CONTRACT")"
echo "canonical sha256: $H_CANON"
[ "$H_CANON" = "$H_IN_REC" ] && echo "[OK] canonical hash matches receipt" || echo "[FAIL] canonical mismatch"
```
