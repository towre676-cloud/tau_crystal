#!/usr/bin/env python3
import json, os, platform, shutil, subprocess, time
from datetime import datetime

def sh(cmd):
    try:
        out = subprocess.check_output(cmd, shell=True, stderr=subprocess.DEVNULL, text=True, timeout=3)
        return out.strip()
    except Exception:
        return ""

def try_int(x, d=None):
    try:
        return int(x)
    except Exception:
        return d

# Load existing passport if present (so we don't clobber fitted coefficients)
path = os.path.join(".tau_ledger","physics","passport.json")
os.makedirs(os.path.dirname(path), exist_ok=True)
doc = {}
if os.path.exists(path):
    try:
        doc = json.load(open(path, "r", encoding="utf-8"))
    except Exception:
        doc = {}

# Host/device basics
cpu_mem = None
try:
    import psutil
    cpu_mem = psutil.virtual_memory().total
except Exception:
    pass

gpu_name, gpu_mem = None, None
if shutil.which("nvidia-smi"):
    q = sh("nvidia-smi --query-gpu=name,memory.total --format=csv,noheader,nounits | head -n 1")
    if q:
        parts = [p.strip() for p in q.split(",")]
        if len(parts) >= 2:
            gpu_name = parts[0]
            gpu_mem = try_int(parts[1]) * 10**6 if parts[1] else None

# Very crude memory bandwidth feeler (kept optional)
beta = doc.get("io",{}).get("beta_sustained_bytes_per_s")
if beta is None:
    try:
        size = min(512*(1<<20), (cpu_mem or (2<<30))//8)
        t0 = time.perf_counter()
        a = bytearray(b"\0") * size
        b = bytearray(a)
        dt = time.perf_counter() - t0
        if dt > 0:
            beta = (2*size)/dt
    except Exception:
        beta = None

# Merge new observations without nuking existing fields
doc.setdefault("host", {})
doc["host"].update({"system": platform.system(), "release": platform.release(), "machine": platform.machine()})

doc.setdefault("cpu", {})
doc["cpu"].update({"mem_total_bytes": cpu_mem})

doc.setdefault("gpu", {})
if gpu_name is not None: doc["gpu"]["name"] = gpu_name
if gpu_mem is not None:  doc["gpu"]["mem_total_bytes"] = gpu_mem

doc.setdefault("io", {})
if beta is not None: doc["io"]["beta_sustained_bytes_per_s"] = beta

doc.setdefault("coefficients", {})
# Preserve previously fitted c_time / c_energy if present; only seed the harmless ones.
if "c_mem" not in doc["coefficients"]:
    doc["coefficients"]["c_mem"] = 1.0
if "E0" not in doc["coefficients"]:
    doc["coefficients"]["E0"] = 0.0

doc["captured_at"] = datetime.now().astimezone().isoformat()

open(path, "w", encoding="utf-8").write(json.dumps(doc, indent=2))
print("[passport] wrote", path)
