import sys, json, time, hashlib, os
import numpy as np

KIND="tau-crystal-receipt"; VERS="1.2.0"; KAPPA=0.1591549431
state={}

def tau_inc(elapsed, slope, tau_min):
    if elapsed<=0: return 0.0
    x=np.tanh(slope*elapsed)
    t=np.arccos(np.clip(1-x,-1,1))/np.pi
    return float(t if t>tau_min else tau_min)

def update(evt, slope, tau_min):
    pid=evt["process_id"]; now=time.time()
    s=state.get(pid)
    if s is None:
        s=state[pid]={"tau":[0.0],"last":now,"prev":"","qcro":[],"ev_sha":"sha256:"+hashlib.sha256(b"").hexdigest(),"pivot":"sha256:"+hashlib.sha256(b"").hexdigest()}
    dt=max(0.0,now-s["last"]); s["last"]=now
    s["tau"].append(round(s["tau"][-1]+tau_inc(dt,slope,tau_min),6))
    seg=str(evt.get("segment","")).lower()
    mode,amp="nominal",0.0
    if "split" in seg: mode,amp="split_receipt",0.6
    if "backorder" in seg: mode,amp="backorder",0.7
    if "rework" in seg: mode,amp="rework",0.5
    s["qcro"].append({"t":s["tau"][-1],"mode":mode,"amp":amp})
    enc=json.dumps(evt,separators=(",",":"),ensure_ascii=False).encode("utf-8")
    s["ev_sha"]="sha256:"+hashlib.sha256((s["ev_sha"]+"|").encode()+enc).hexdigest()
    return s

def residue(qs):
    a=[q["amp"] for q in qs[-8:]]; 
    if not a: return 0.0,0.0
    v=np.asarray(a,float); R=float(np.linalg.norm(v)); D=float(np.linalg.norm(v-v.mean()))
    return R,D

def main():
    tau_min=float(os.getenv("TAU_MIN","0.05")); slope=float(os.getenv("TAU_SLOPE","0.25"))
    for line in sys.stdin:
        line=line.strip()
        if not line: continue
        try:
            evt=json.loads(line)
            if "process_id" not in evt: continue
            s=update(evt,slope,tau_min)
            now=time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
            Rn,Dn=residue(s["qcro"])
            doc={
              "kind":KIND,"version":VERS,
              "process":{"id":evt["process_id"],"domain":evt.get("domain","UNK"),"segment":evt.get("segment","event"),"prev_manifest":s["prev"]},
              "tau":{"t":s["tau"],"clock":"Chebyshev-decay","params":{"tau_min":tau_min,"slope":slope}},
              "residue":{"R_norm":Rn,"D_norm":Dn,"kappa":KAPPA,"qcro":s["qcro"][-4:]},
              "witness":{"events_sha":s["ev_sha"],"pivot_transcript":s["pivot"],"rank_signature":{"p":2147482951,"rank":6}},
              "sustainability":evt.get("sustainability",{}),
              "attest":{"merkle_root":"","signed_by":"","timestamp":now}
            }
            payload=json.dumps(doc,separators=(",",":"),ensure_ascii=False)
            digest="sha256:"+hashlib.sha256(payload.encode("utf-8")).hexdigest()
            doc["attest"]["merkle_root"]=digest
            out=json.dumps(doc,ensure_ascii=False)
            s["prev"]=digest
            sys.stdout.write(out+"\n"); sys.stdout.flush()
        except Exception as e:
            sys.stderr.write(f"[sidecar] {e}\n"); sys.stderr.flush()
if __name__=="__main__": main()
