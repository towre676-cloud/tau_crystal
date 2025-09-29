cd "$HOME/Desktop/tau_crystal/tau_crystal" || exit 1
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
rec="${1:-analysis/capsules/demo/receipt.json}"; shift || true
: "${PY:=python}"
$PY - <<PY || { echo "[err] Python couple/merge failed"; exit 1; }
import json,sys,os
p=sys.argv[1] if len(sys.argv)>1 else "analysis/capsules/demo/receipt.json"
d=json.load(open(p,"rb"))
d["seifert_coupled"]=True
os.makedirs(os.path.dirname(p),exist_ok=True); json.dump(d,open(p,"w"),indent=2)
PY
