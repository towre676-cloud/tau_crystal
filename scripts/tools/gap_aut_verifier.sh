#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022
IN="${1:-}"; OUT="${2:-}"
[ -n "${IN}" ] && [ -n "${OUT}" ] && [ -f "${IN}" ] || { printf '{"ok":false,"error":"usage: gap_aut_verifier.sh <in.json> <out.json)"}\n' > "${OUT:-/dev/stdout}"; exit 2; }

# dependencies: python3 and a working "gap" in PATH (native or shim)
if ! command -v python3 >/dev/null 2>&1; then printf '{"ok":false,"error":"python3_not_found"}\n' > "$OUT"; exit 0; fi
if ! command -v gap >/dev/null 2>&1; then printf '{"ok":false,"error":"gap_not_found"}\n' > "$OUT"; exit 0; fi

read -r EXP INHASH <<PYOUT
$(python3 - "$IN" <<'PY'
import json,sys,hashlib
d=json.load(open(sys.argv[1],'r',encoding='utf-8'))
exp=d.get("expected",{}).get("aut_size",432)  # default 432
h=hashlib.sha256(json.dumps(d,sort_keys=True,separators=(",",":")).encode()).hexdigest()
print(exp); print(h)
PY
)
PYOUT

OBS="$(gap -q <<'GAP'
G := SmallGroup(27,3);;
A := AutomorphismGroup(G);;
Print(Size(A));
GAP
)" || OBS="0"

python3 - <<PY > "$OUT"
import json,sys,datetime
exp=int("${EXP}" or 0); obs=int("${OBS}" or 0)
ok = (obs==exp)
print(json.dumps({
  "ok": ok,
  "kind": "tau-crystal.group.aut",
  "timestamp": datetime.datetime.utcnow().replace(microsecond=0).isoformat()+"Z",
  "input_sha256": "${INHASH}",
  "observed_aut": obs,
  "expected_aut": exp
}, separators=(",",":")))
PY
