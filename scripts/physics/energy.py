#!/usr/bin/env python3
import os, glob, time

def _read_u64(path):
    try:
        with open(path,"r") as f:
            return int(f.read().strip())
    except Exception:
        return None

def rapl_joules_snapshot():
    """Sum energy_uj across sockets/domains (Linux RAPL). Return Joules or None."""
    roots = glob.glob("/sys/class/powercap/intel-rapl:*")
    if not roots:
        return None
    total_uj = 0
    saw = False
    for root in roots:
        for p in glob.glob(os.path.join(root, "**", "energy_uj"), recursive=True):
            val = _read_u64(p)
            if val is not None:
                total_uj += val
                saw = True
    return (total_uj / 1e6) if saw else None

def measure_energy(run_fn, *args, **kwargs):
    """Call run_fn(); return (result, energy_J or None, elapsed_s)."""
    pre = rapl_joules_snapshot()
    t0 = time.perf_counter()
    try:
        out = run_fn(*args, **kwargs)
    finally:
        pass
    t1 = time.perf_counter()
    post = rapl_joules_snapshot()
    if pre is None or post is None:
        return out, None, (t1 - t0)
    E = max(0.0, post - pre)  # simple non-negative clamp
    return out, E, (t1 - t0)
