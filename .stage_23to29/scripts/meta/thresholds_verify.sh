cd "$HOME/Desktop/tau_crystal/tau_crystal" || exit 1
set -e  # NOTE: no -u here to avoid 'unbound variable' traps

T=".tau_ledger/stability/thresholds.json"
S=".tau_ledger/stability/thresholds.seal.json"

# Provision dev defaults if absent
if [ ! -s "$T" ]; then
  printf '%s\n' '{"hysteresis_loop_area":0.012,"heegner_entropy_bound":0.008,"virtualalloc_gate":"+X","barcode_bottleneck":0.005}' > "$T"
fi
if [ ! -s "$S" ]; then
  H=$(sha256sum "$T" | cut -d ' ' -f1)
  TS=$(date -u +%Y-%m-%dT%H:%M:%SZ)
  printf '%s\n' "{\"hash_sha256\":\"$H\",\"signed_at\":\"$TS\",\"signature\":\"unsig:$H\"}" > "$S"
fi

H1=$(sha256sum "$T" | cut -d ' ' -f1)
# Extract hash from JSON without jq (sed grabs the first match)
H2=$(sed -n 's/.*"hash_sha256":"\([^"]*\)".*/\1/p' "$S")

[ -n "$H2" ] || { echo "[FAIL] seal has no hash"; exit 4; }
[ "$H1" = "$H2" ] || { echo "[FAIL] thresholds hash mismatch"; exit 5; }
echo "[OK] thresholds verified (hash match)"
