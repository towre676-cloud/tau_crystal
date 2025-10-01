#!/usr/bin/env python3
# Deterministic toy emitting a τ-pulse
import json, math, sys, time
seed=42; steps=64; data=[]
for k in range(steps):
    t = -1 + 2*k/(steps-1)
    data.append(math.cos(steps*math.acos(t)))
tau = sum(x*x for x in data)/len(data)
manifest={
  "tau_pulse": round(tau,8),
  "seed": seed,
  "steps": steps,
  "commit": (sys.argv[1] if len(sys.argv)>1 else "unknown"),
  "timestamp_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())}
print(json.dumps(manifest, indent=2))
