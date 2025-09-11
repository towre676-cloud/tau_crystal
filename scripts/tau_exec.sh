#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022

REQ_RAW="${1-}"
REQ="${REQ_RAW//$'\r'/}"

if [ -z "${REQ}" ] || [ ! -f "${REQ}" ]; then
  echo "dispatch: BAD REQUEST PATH. raw='${REQ_RAW}' trimmed='${REQ}' pwd='$(pwd)'" >&2
  echo '{"ok":false,"error":"usage: tau_exec.sh <request.json>"}'
  exit 2
fi

rf(){ python3 - "$REQ" 2>/dev/null <<'PY' || echo ""
import json,sys; d=json.load(open(sys.argv[1], "r", encoding="utf-8"))
print(d.get("tool","")); print(d.get("input_path","")); print(d.get("output_path",""))
PY
}

readarray -t F < <(rf) || true
t="${F[0]:-}"; in="${F[1]:-}"; out="${F[2]:-}"
t=${t//$'\r'/}; in=${in//$'\r'/}; out=${out//$'\r'/}

mkdir -p "$(dirname -- "$out")" 2>/dev/null || true
echo "dispatch:$t -> $in -> $out" >&2

case "$t" in
  physics_verifier)     bash scripts/tools/physics_verifier.sh       "$in" "$out" || true ;;
  delta27_verifier)     bash scripts/tools/delta27_verifier.sh       "$in" "$out" || true ;;
  gap_aut_verifier)     bash scripts/tools/gap_aut_verifier.sh       "$in" "$out" || true ;;
  cp_residual_verifier) bash scripts/tools/cp_residual_verifier.sh   "$in" "$out" || true ;;
  cp_unitary_verifier)  bash scripts/tools/cp_unitary_verifier.sh    "$in" "$out" || true ;;
  cp_residual_symm_verifier) bash scripts/tools/cp_residual_symm_verifier.sh "$in" "$out" || true ;;
  tm_sumrule_gate)     bash scripts/tools/tm_sumrule_gate.sh        "$in" "$out" || true ;;
  *) echo '{"ok":false,"error":"unsupported_tool"}'; exit 4 ;;
esac

python3 - "$REQ" "$out" 2>/dev/null <<'PY' || cat -- "$out"
import json,sys,hashlib
o=json.load(open(sys.argv[2],'r',encoding='utf-8'))
h=hashlib.sha256(open(sys.argv[1],'rb').read()).hexdigest()
o["request_sha256"]=h
print(json.dumps(o,separators=(",",":")))
PY
