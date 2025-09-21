#!/usr/bin/env bash
set +H
. scripts/plumbing/_lib.sh || exit 1
BOX="${1:?box}"; P="${2:?prime}"; STEPS="${3:-96}"; RAD="${4:-0.02}"; HEK="${5:-0.0}"; FRAME="${6:-0}"
safe_mkdir ".tau_ledger/hysteresis/$BOX/p$P"
fwd=".tau_ledger/hysteresis/$BOX/p$P/fwd.csv"; rev=".tau_ledger/hysteresis/$BOX/p$P/rev.csv"
: > "$fwd"; : > "$rev"
base=$(python -c "import sys; p=int(sys.argv[1]); print(1.0 + 1.0/(p+1))" "$P" 2>/dev/null)
i=0; while [ $i -lt "$STEPS" ]; do
  t=$(python -c "import math,sys; i=int(sys.argv[1]); n=int(sys.argv[2]); print(2*math.pi*i/max(1,n-1))" "$i" "$STEPS" 2>/dev/null)
  q=$(python -c "import math,sys; b=float(sys.argv[1]); r=float(sys.argv[2]); t=float(sys.argv[3]); print(b + r*math.cos(t))" "$base" "$RAD" "$t" 2>/dev/null)
  z=$(python -c "import sys,math,hashlib,random; q=float(sys.argv[1]); h=float(sys.argv[2]); fr=float(sys.argv[3]); tag=sys.argv[4]; seed=f\"{q:.12f}|{h:.12f}|{fr:.12f}|{tag}\"; rnd=random.Random(int(hashlib.sha256(seed.encode()).hexdigest(),16)%2**32); phase=0.07*math.sin(2*math.pi*math.log(max(q,1e-12)))+0.05*math.sin(2*math.pi*h); frame=0.03*math.sin(math.pi*fr); noise=(rnd.random()-0.5)*0.001; print(phase+frame+noise)" "$q" "$HEK" "$FRAME" "p$P-fwd" 2>/dev/null)
  printf "%s,%s,%s,%s\n" "$i" "$q" "$HEK" "$z" >> "$fwd"
  i=$((i+1))
done
i=0; while [ $i -lt "$STEPS" ]; do
  t=$(python -c "import math,sys; i=int(sys.argv[1]); n=int(sys.argv[2]); print(2*math.pi*(1 - i/max(1,n-1)))" "$i" "$STEPS" 2>/dev/null)
  q=$(python -c "import math,sys; b=float(sys.argv[1]); r=float(sys.argv[2]); t=float(sys.argv[3]); print(b + r*math.cos(t))" "$base" "$RAD" "$t" 2>/dev/null)
  z=$(python -c "import sys,math,hashlib,random; q=float(sys.argv[1]); h=float(sys.argv[2]); fr=float(sys.argv[3]); tag=sys.argv[4]; seed=f\"{q:.12f}|{h:.12f}|{fr:.12f}|{tag}\"; rnd=random.Random(int(hashlib.sha256(seed.encode()).hexdigest(),16)%2**32); phase=0.07*math.sin(2*math.pi*math.log(max(q,1e-12)))+0.05*math.sin(2*math.pi*h); frame=0.03*math.sin(math.pi*fr); noise=(rnd.random()-0.5)*0.001; print(phase+frame+noise)" "$q" "$HEK" "$FRAME" "p$P-rev" 2>/dev/null)
  printf "%s,%s,%s,%s\n" "$i" "$q" "$HEK" "$z" >> "$rev"
  i=$((i+1))
done
Hp=$(python -c "import sys,csv; f1,f2=sys.argv[1],sys.argv[2]; rf=list(csv.reader(open(f1))); rr=list(csv.reader(open(f2))); zf=sum(float(x[3]) for x in rf)/max(1,len(rf)); zr=sum(float(x[3]) for x in rr)/max(1,len(rr)); print(zf-zr)" "$fwd" "$rev" 2>/dev/null)
rec=".tau_ledger/hysteresis/$BOX/p$P/hysteresis_p.json"
write_json "$rec" "box" "$BOX" "prime" "$P" "steps" "$STEPS" "radius" "$RAD" "hecke" "$HEK" "frame" "$FRAME" "H_p" "$Hp" "created_at" "$(date -u +%Y-%m-%dT%H:%M:%SZ)"
log "hysteresis_prime: box=$BOX p=$P H_p=$Hp -> $rec"
