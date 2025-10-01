#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
d=".tau_ledger/freed"; [ -d "$d" ] || { echo "[no ledger]"; exit 0; }
echo "== Freed ledger index =="; echo
LF=$(printf "%s\n" "$d"/lean_build_*.json 2>/dev/null | LC_ALL=C sort | tail -n1)
[ -f "$LF" ] && jq -r "\"lean_build  :: stamp=\(.stamp)  ok=\(.build_ok)  merkle=\(.olean_merkle)\"" "$LF" || echo "lean_build  :: (none)"
PF=$(printf "%s\n" "$d"/phi_pullback_*.json 2>/dev/null | LC_ALL=C sort | tail -n1)
[ -f "$PF" ] && jq -r "\"phi_pullback:: stamp=\(.stamp)  pass=\(.pass)  proof_build=\(.proof_build // \"-\")\"" "$PF" || echo "phi_pullback:: (none)"
TMF=$(printf "%s\n" "$d"/tmf_sigma_*.json 2>/dev/null | LC_ALL=C sort | tail -n1)
[ -f "$TMF" ] && jq -r "\"tmf_sigma  :: stamp=\(.stamp)  kind=\(.sigma_orientation)  proof_build=\(.proof_build // \"-\")\"" "$TMF" || echo "tmf_sigma  :: (none)"
ZR=$(printf "%s\n" "$d"/z4c_resstudy_*.json 2>/dev/null | LC_ALL=C sort | tail -n1)
if [ -f "$ZR" ]; then
  echo
  echo "z4c_resstudy::"
  jq -r '"  stamp=\(.stamp)  test=\(.test)  stable=\(.stable)"' "$ZR"
  jq -r '"  orders(H,M,CG)=\(.orders.H // "-"),\(.orders.M // "-"),\(.orders.C_Gamma // "-")"' "$ZR"
  echo "  deltas:"
  jq -r '.deltas[] | "    res=\(.res)  ΔH=\(.H)  ΔM=\(.M)  ΔCΓ=\(."C_Gamma")"' "$ZR"
else
  echo "z4c_resstudy:: (none)"
fi
