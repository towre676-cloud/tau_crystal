#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
g0="${1:-0.1}"; ell="${2:-0.5}"; b="${3:-1.3}"; b1="${4:-0.7}"
OUT_DIR=".tau_ledger/rgflow"; mkdir -p "$OUT_DIR"
TS="$(date -u +%Y%m%dT%H%M%SZ)"
JSON="$(scripts/flow/two_loop_solver.py "$g0" "$ell" "$b" "$b1")"
echo "$TS" > "$OUT_DIR/ts.txt"
REC="$OUT_DIR/receipt.tsv"
if [ ! -f "$REC" ]; then printf "%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n" \
  "kind" "g0" "ell" "b" "b1" "g" "residual_or_invariant" "extras" > "$REC"; fi
one_g=$(python3 - <<'PY'\nimport json,sys\nj=json.loads(sys.argv[1]);print(j.get('one',{}).get('g',''))\nPY\n"$JSON")
one_inv=$(python3 - <<'PY'\nimport json,sys\nj=json.loads(sys.argv[1]);print(j.get('one',{}).get('invariant',''))\nPY\n"$JSON")
two_g=$(python3 - <<'PY'\nimport json,sys\nj=json.loads(sys.argv[1]);print(j.get('two',{}).get('g',''))\nPY\n"$JSON")
two_res=$(python3 - <<'PY'\nimport json,sys\nj=json.loads(sys.argv[1]);print(j.get('two',{}).get('residual',''))\nPY\n"$JSON")
Nval=$(python3 - <<'PY'\nimport json,sys\nj=json.loads(sys.argv[1]);print(j.get('N',''))\nPY\n"$JSON")
Lgeo=$(python3 - <<'PY'\nimport json,sys\nj=json.loads(sys.argv[1]);print(j.get('L_geo',''))\nPY\n"$JSON")
Sone=$(python3 - <<'PY'\nimport json,sys\nj=json.loads(sys.argv[1]);print(j.get('S_one',''))\nPY\n"$JSON")
Stwo=$(python3 - <<'PY'\nimport json,sys\nj=json.loads(sys.argv[1]);print(j.get('S_two',''))\nPY\n"$JSON")
MDAG=$(python3 - <<'PY'\nimport json,sys\nj=json.loads(sys.argv[1]);print(j.get('MU_DAGGER',''))\nPY\n"$JSON")
printf "%s\t%s\t%s\t%s\t%s\t%s\t%s\tN=%s;L_geo=%s;S_one=%s;S_two=%s;MU_DAGGER=%s\n" \
  "one" "$g0" "$ell" "$b" "$b1" "$one_g" "$one_inv" "$Nval" "$Lgeo" "$Sone" "$Stwo" "$MDAG" >> "$REC"
printf "%s\t%s\t%s\t%s\t%s\t%s\t%s\tN=%s;L_geo=%s;S_one=%s;S_two=%s;MU_DAGGER=%s\n" \
  "two" "$g0" "$ell" "$b" "$b1" "$two_g" "$two_res" "$Nval" "$Lgeo" "$Sone" "$Stwo" "$MDAG" >> "$REC"
sha256sum "$REC" | awk '{print $1}' > "$OUT_DIR/receipt.sha256"
