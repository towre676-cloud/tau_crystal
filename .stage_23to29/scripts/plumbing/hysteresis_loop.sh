#!/usr/bin/env bash
set +H
. scripts/plumbing/_lib.sh || exit 1
BOX="${1:?box}"; STEPS="${2:-96}"; Q0="${3:-1.0}"; AMP="${4:-0.07}"; HEK="${5:-0.0}"; FRAME="${6:-0}"
safe_mkdir ".tau_ledger/hysteresis/$BOX"
fwd=".tau_ledger/hysteresis/$BOX/fwd.csv"; rev=".tau_ledger/hysteresis/$BOX/rev.csv"
: > "$fwd"; : > "$rev"
i=0; while [ $i -lt "$STEPS" ]; do
  t=$(python -c "import math,sys; i=int(sys.argv[1]); n=int(sys.argv[2]); print(2*math.pi*i/max(1,n-1))" "$i" "$STEPS" 2>/dev/null)
  q=$(python -c "import math,sys; q0=float(sys.argv[1]); a=float(sys.argv[2]); t=float(sys.argv[3]); print(q0 + a*math.cos(t))" "$Q0" "$AMP" "$t" 2>/dev/null)
  z=$(python -c "import sys,math,hashlib,random; q=float(sys.argv[1]); h=float(sys.argv[2]); fr=float(sys.argv[3]); tag=sys.argv[4]; seed=f\"{q:.12f}|{h:.12f}|{fr:.12f}|{tag}\"; rnd=random.Random(int(hashlib.sha256(seed.encode()).hexdigest(),16)%2**32); phase=0.07*math.sin(2*math.pi*math.log(max(q,1e-12)))+0.05*math.sin(2*math.pi*h); frame=0.03*math.sin(math.pi*fr); noise=(rnd.random()-0.5)*0.001; print(phase+frame+noise)" "$q" "$HEK" "$FRAME" "fwd" 2>/dev/null)
  printf "%s,%s,%s,%s\n" "$i" "$q" "$HEK" "$z" >> "$fwd"
  i=$((i+1))
done
i=0; while [ $i -lt "$STEPS" ]; do
  t=$(python -c "import math,sys; i=int(sys.argv[1]); n=int(sys.argv[2]); print(2*math.pi*(1 - i/max(1,n-1)))" "$i" "$STEPS" 2>/dev/null)
  q=$(python -c "import math,sys; q0=float(sys.argv[1]); a=float(sys.argv[2]); t=float(sys.argv[3]); print(q0 + a*math.cos(t))" "$Q0" "$AMP" "$t" 2>/dev/null)
  z=$(python -c "import sys,math,hashlib,random; q=float(sys.argv[1]); h=float(sys.argv[2]); fr=float(sys.argv[3]); tag=sys.argv[4]; seed=f\"{q:.12f}|{h:.12f}|{fr:.12f}|{tag}\"; rnd=random.Random(int(hashlib.sha256(seed.encode()).hexdigest(),16)%2**32); phase=0.07*math.sin(2*math.pi*math.log(max(q,1e-12)))+0.05*math.sin(2*math.pi*h); frame=0.03*math.sin(math.pi*fr); noise=(rnd.random()-0.5)*0.001; print(phase+frame+noise)" "$q" "$HEK" "$FRAME" "rev" 2>/dev/null)
  printf "%s,%s,%s,%s\n" "$i" "$q" "$HEK" "$z" >> "$rev"
  i=$((i+1))
done
H=$(python -c "import sys,csv; f1,f2=sys.argv[1],sys.argv[2]; rf=list(csv.reader(open(f1))); rr=list(csv.reader(open(f2))); zf=sum(float(x[3]) for x in rf)/max(1,len(rf)); zr=sum(float(x[3]) for x in rr)/max(1,len(rr)); print(zf-zr)" "$fwd" "$rev" 2>/dev/null)
rec=".tau_ledger/hysteresis/$BOX/hysteresis.json"
write_json "$rec" "box" "$BOX" "steps" "$STEPS" "q0" "$Q0" "amp" "$AMP" "hecke" "$HEK" "frame" "$FRAME" "H" "$H" "created_at" "$(date -u +%Y-%m-%dT%H:%M:%SZ)"
log "hysteresis_loop: box=$BOX H=$H fwd=$fwd rev=$rev -> $rec"
