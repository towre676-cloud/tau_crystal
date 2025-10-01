#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
LED=".tau_ledger/freed"

jq --version >/dev/null 2>&1 || { echo "[err] jq missing"; exit 1; }

# lean receipt must be good
LEAN=$(printf "%s\n" "$LED"/lean_build_*.json 2>/dev/null | LC_ALL=C sort | tail -n1)
[ -f "$LEAN" ] || { echo "[err] no lean_build_*.json"; exit 1; }
OK=$(jq -r ".build_ok" "$LEAN"); MERKLE=$(jq -r ".olean_merkle" "$LEAN")
[ "$OK" = "1" ] || { echo "[err] Lean build_ok!=1"; jq . "$LEAN"; exit 1; }
[ "$MERKLE" != "unbuilt" ] || { echo "[err] Lean olean_merkle=unbuilt"; exit 1; }

# latest resstudy
RST=$(printf "%s\n" "$LED"/z4c_resstudy_*.json 2>/dev/null | LC_ALL=C sort | tail -n1)
[ -f "$RST" ] || { echo "[err] no z4c_resstudy_*.json"; exit 1; }

stable=$(jq -r ".stable" "$RST")
[ "$stable" = "true" ] || { echo "[err] resstudy not stable"; jq . "$RST"; exit 1; }

# thresholds
ORD_MIN=${ORD_MIN:-0.25}
EPS=${EPS:-1e-12}

IH=$(jq -r ".I_orders.H" "$RST"); IM=$(jq -r ".I_orders.M" "$RST"); IC=$(jq -r ".I_orders.C_Gamma" "$RST")
python - "$IH" "$IM" "$IC" "$ORD_MIN" <<'PY' || exit 1
import sys
IH,IM,IC = map(float, sys.argv[1:4]); ORD_MIN=float(sys.argv[4])
bad=[(lab,val) for lab,val in [("H",IH),("M",IM),("C_Gamma",IC)] if not (val==val and val>=ORD_MIN)]
if bad:
  print("[err] low integrated orders:", bad); raise SystemExit(1)
print("[ok] orders:", dict(H=IH,M=IM,C_Gamma=IC))
PY

# deltas must be >= -EPS across all resolutions (integrated metrics)
NEG=$(jq -r --arg eps "$EPS" '.deltas[] | select(.IH < (0 - ($eps|tonumber)) or .IM < (0 - ($eps|tonumber)) or .ICG < (0 - ($eps|tonumber)))' "$RST" | wc -l | awk '{print $1}')
if [ "$NEG" -ne 0 ]; then
  echo "[err] negative integrated deltas beyond tolerance"; jq . "$RST"; exit 1
fi

echo "[ok] CI guard passed: merkle=$MERKLE; resstudy=$(basename "$RST")"
