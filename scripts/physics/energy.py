#!/usr/bin/env python3
import os, glob

def _read_u64(p):
    try:
        with open(p, "r") as f:
            return int(f.read().strip())
    except Exception:
        return None

def rapl_joules_snapshot():
    """Return total joules from RAPL counters, or None if unavailable."""
    roots = glob.glob("/sys/class/powercap/intel-rapl:*")
    if not roots:
        return None
    total_uj, saw = 0, False
    for root in roots:
        for p in glob.glob(os.path.join(root, "**", "energy_uj"), recursive=True):
            v = _read_u64(p)
            if v is not None:
                total_uj += v
                saw = True
    return (total_uj / 1e6) if saw else None
