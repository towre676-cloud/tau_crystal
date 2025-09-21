#!/usr/bin/env bash
set +H
. scripts/plumbing/_lib.sh || exit 1
BOX="${1:?box}"
c=".tau_ledger/hysteresis/$BOX/hysteresis.json"; [ -f "$c" ] || { echo "no complex hysteresis"; exit 0; }
Hp=$(python -c "import sys,glob,json; s=0.0\nimport glob as G\nfor p in G.glob(f\".tau_ledger/hysteresis/{sys.argv[1]}/p*/hysteresis_p.json\"):\n  try:\n    s+=float(json.load(open(p)).get(\"H_p\",0))\n  except Exception:\n    pass\nprint(s)" "$BOX" 2>/dev/null)
H=$(python -c "import sys,json; print(float(json.load(open(sys.argv[1]))[\"H\"]))" "$c" 2>/dev/null)
DELTA=$(python -c "import sys; H=float(sys.argv[1]); Hp=float(sys.argv[2]); print(abs(H)-abs(Hp))" "$H" "$Hp" 2>/dev/null)
printf "verify: complex H=%s, sum local H_p=%s, delta=%s\n" "$H" "$Hp" "$DELTA"
log "verify_hysteresis: $BOX H=$H sum(H_p)=$Hp"
