#!/usr/bin/env bash
cd "$HOME/Desktop/tau_crystal/tau_crystal" || exit 1
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
targets=("$@")
if [ ${#targets[@]} -eq 0 ]; then
  mapfile -t targets < <(find src/Spectral -maxdepth 1 -type f -name "*.lean" | sort)
fi
for rel in "${targets[@]}"; do
  [ -f "$rel" ] || { echo "[skip] not a file: $rel"; continue; }
  case "$rel" in ./*) rel="${rel#./}";; esac
  mod="${rel%.lean}"; mod="${mod//\//.}"   # e.g. src.Spectral.Core
  echo
  echo "────────────────────────────────────────────────────────"
  echo "[triage] $rel  (module: $mod)"
  # run capsule build for this single file
  bash scripts/meta/capsule_one.sh "$rel" || true
  # locate its build log and capsule json
  tag="${mod//./_}"
  blog=".cache/capsules/_build_${tag}.log"
  cjson=".tau_ledger/lean_module_capsules/${tag}.json"
  # print capsule verdict summary
  if [ -s "$cjson" ]; then
    ok=$(grep -m1 "\"build_ok\":" "$cjson" | sed -E "s/.*\"build_ok\":([0-9]+).*/\\1/")
    ms=$(grep -m1 "\"build_time_ms\":" "$cjson" | sed -E "s/.*\"build_time_ms\":([0-9]+).*/\\1/")
    echo "[capsule] build_ok=$ok  ms=$ms  json=$cjson"
  else
    echo "[capsule] no JSON found: $cjson"
  fi
  # extract first Lean error with a short context
  if [ -s "$blog" ]; then
    ln=$(grep -n -m1 "error:" "$blog" | cut -d: -f1 || true)
    if [ -n "${ln:-}" ]; then
      s=$(( ln>5 ? ln-5 : 1 ))
      e=$(( ln+15 ))
      echo "[error] first error in $blog (lines $s..$e):"
      sed -n "${s},${e}p" "$blog"
    else
      echo "[error] no \"error:\" lines; showing last 40 lines of $blog"
      tail -n 40 "$blog"
    fi
  else
    echo "[log] missing or empty: $blog"
  fi
done
