#!/usr/bin/env bash
set -euo pipefail
set +H
umask 022
export LC_ALL=C LANG=C

need() { command -v "$1" >/dev/null 2>&1 || { echo "[err] missing tool: $1"; exit 1; }; }
need jq

LED=".tau_ledger/freed"
[ -d "$LED" ] || { echo "[err] ledger missing: $LED"; exit 1; }

LEAN=$(printf "%s\n" "$LED"/lean_build_*.json 2>/dev/null | LC_ALL=C sort | tail -n1)
[ -f "$LEAN" ] || { echo "[err] no lean_build_*.json"; exit 1; }

OK=$(jq -r '.build_ok' "$LEAN")
MERKLE=$(jq -r '.olean_merkle' "$LEAN")
[ "$OK" = "1" ] || { echo "[err] Lean build_ok!=1"; cat "$LEAN"; exit 1; }
[ "$MERKLE" != "unbuilt" ] || { echo "[err] Lean olean_merkle=unbuilt"; cat "$LEAN"; exit 1; }

PF=$(printf "%s\n" "$LED"/phi_pullback_*.json 2>/dev/null | LC_ALL=C sort | tail -n1)
[ -f "$PF" ] || { echo "[err] no phi_pullback_*.json"; exit 1; }
jq -e '.pass==true' "$PF" >/dev/null || { echo "[err] PF pass!=true"; cat "$PF"; exit 1; }
jq -e --arg m "$MERKLE" '.proof_build==$m' "$PF" >/dev/null || { echo "[err] PF proof_build mismatch"; cat "$PF"; exit 1; }

TMF=$(printf "%s\n" "$LED"/tmf_sigma_*.json 2>/dev/null | LC_ALL=C sort | tail -n1)
[ -f "$TMF" ] || { echo "[err] no tmf_sigma_*.json"; exit 1; }
jq -e --arg m "$MERKLE" '.proof_build==$m' "$TMF" >/dev/null || { echo "[err] tmf proof_build mismatch"; cat "$TMF"; exit 1; }
CSV=$(jq -r '.csv' "$TMF")
[ -f "$CSV" ] || { echo "[err] tmf CSV missing: $CSV"; cat "$TMF"; exit 1; }
head -n 1 "$CSV" | grep -q '^n,a_n$' || { echo "[err] tmf CSV header not found in $CSV"; head -n 3 "$CSV"; exit 1; }

echo "[ok] CI guard passed: merkle=$MERKLE"
