#!/usr/bin/env bash
PY="$(command -v python3 || command -v python || true)"
CSV="${1:-}"; MAN="${2:-}"; NMAX="${3:-64}"; CONF="${4:-0.95}"
[ -z "$CSV" ] && { echo "[laurent] need CSV path"; exit 0; }
[ -z "$MAN" ] && { echo "[laurent] need manifest.json path"; exit 0; }
[ ! -f "$CSV" ] && { echo "[laurent] CSV not found: $CSV"; exit 0; }
[ ! -f "$MAN" ] && { echo "[laurent] manifest not found: $MAN"; exit 0; }
[ -z "$PY" ] && { echo "[laurent] Python not found; skipping"; exit 0; }

SIG="$("$PY" scripts/laurent/laurent_ring.py "$CSV" "$NMAX" "$CONF" 2>/dev/null)"
echo "$SIG" | grep -q '"error"' && { echo "[laurent] skipped: $SIG"; exit 0; }

# Merge via Python & refresh Merkle (CORE only)
"$PY" - "$MAN" <<'PY'
import sys, json, hashlib, datetime
man_path=sys.argv[1]
doc=json.load(open(man_path,encoding='utf-8'))
sig=json.loads(sys.stdin.read())
doc['laurent_signature']=sig
core=dict(doc); core.pop('attest',None)
digest=hashlib.sha256(json.dumps(core,separators=(',',':'),sort_keys=True).encode()).hexdigest()
doc.setdefault('attest',{})
doc['attest']['merkle_root']="sha256:"+digest
doc['attest']['timestamp']=datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
open(man_path,'w',encoding='utf-8').write(json.dumps(doc,ensure_ascii=False,indent=2))
print("sha256:"+digest)
PY

# Brief readout (safe even if keys missing)
"$PY" - "$MAN" <<'PY'
import sys,json
doc=json.load(open(sys.argv[1],encoding='utf-8'))
ls=doc.get("laurent_signature",{})
ts=ls.get("tau_series",{})
print("[tau] radii:", ts.get("radii",[]))
print("[tau] Δτ:", ts.get("delta_tau",[]))
PY
