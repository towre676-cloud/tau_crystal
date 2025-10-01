#!/usr/bin/env python3
import csv, json, re, os, time
from pathlib import Path

root = Path('.').resolve()
census_in  = root/'.tau_ledger'/'census'/'census.tsv'
census_out = root/'.tau_ledger'/'census'/'census_full.tsv'

# Where to look globally in addition to local dirs
GLOBAL_HINT_DIRS = [
    root/'analysis'/'morpho', root/'analysis',
    root/'_fusion_out', root/'receipts', root/'_verify',
    root/'certs', root/'spectral_kernel', root/'scripts'
]

conv_re_json_key = re.compile(r'convexity', re.I)
sym_re_json_key  = re.compile(r'(symmetry|bilateral).*rms', re.I)
conv_re_text     = re.compile(r'convexity\s*=\s*([0-9]+(?:\.[0-9]+)?)', re.I)
sym_re_text      = re.compile(r'(?:symmetry|bilateral).*?rms\s*=\s*([0-9]+(?:\.[0-9]+)?)', re.I)

def safe_json_load(p: Path):
    try:
        with p.open('r', encoding='utf-8', errors='ignore') as f:
            return json.load(f)
    except Exception:
        return None

def scan_file_for_metrics(p: Path):
    """Return (conv, sym) found in a single file; None/None if absent."""
    name = p.name.lower()
    suf  = p.suffix.lower()
    conv = sym = None
    if suf == '.json':
        data = safe_json_load(p)
        if isinstance(data, dict):
            for k, v in data.items():
                lk = k.lower()
                if conv is None and conv_re_json_key.search(lk):
                    try: conv = float(v)
                    except: pass
                if sym is None and sym_re_json_key.search(lk):
                    try: sym = float(v)
                    except: pass
    elif suf in ('.tsv', '.csv'):
        try:
            with p.open('r', encoding='utf-8', errors='ignore') as f:
                head = f.readline()
                if not head: return None, None
                sep = '\t' if '\t' in head else ','
                cols = [c.strip().lower() for c in head.strip().split(sep)]
                iC = next((i for i,c in enumerate(cols) if 'convexity' in c), None)
                iS = next((i for i,c in enumerate(cols) if 'rms' in c and ('symmetry' in c or 'bilateral' in c)), None)
                for line in f:
                    parts = [x.strip() for x in line.strip().split(sep)]
                    if conv is None and iC is not None and iC < len(parts):
                        try: conv = float(parts[iC])
                        except: pass
                    if sym is None and iS is not None and iS < len(parts):
                        try: sym = float(parts[iS])
                        except: pass
        except Exception:
            pass
    elif suf in ('.log', '.txt'):
        try:
            with p.open('r', encoding='utf-8', errors='ignore') as f:
                for line in f:
                    if conv is None:
                        m = conv_re_text.search(line)
                        if m: conv = float(m.group(1))
                    if sym is None:
                        m = sym_re_text.search(line)
                        if m: sym = float(m.group(1))
        except Exception:
            pass
    return conv, sym

def candidate_files(start: Path):
    """Yield files to inspect in priority order."""
    # Highest priority: same dir, then parent, then grandparent
    yield from (start.parent.iterdir() if start.parent.exists() else [])
    if start.parent.parent.exists():
        yield from start.parent.parent.iterdir()
    # Then global hint dirs (flat scan of each dir)
    for d in GLOBAL_HINT_DIRS:
        if d.exists():
            for p in d.rglob('*'):
                if p.is_file():
                    yield p

def score_file_for(start: Path, p: Path):
    """Higher is better: prefer local, then time‑recent, then filename hints."""
    try: mt = p.stat().st_mtime
    except: mt = 0.0
    # locality
    if p.parent == start.parent: loc = 3
    elif p.parent == start.parent.parent: loc = 2
    else: loc = 1
    # filename hint
    name = p.name.lower()
    hint = 1 if ('metric' in name or 'fusion' in name or 'face' in name) else 0
    return (loc, mt, hint)

def best_metrics_for_trace(trace_path: Path):
    best = None
    best_score = None
    for p in candidate_files(trace_path):
        if p.suffix.lower() not in ('.json', '.tsv', '.csv', '.log', '.txt'): 
            continue
        conv, sym = scan_file_for_metrics(p)
        if conv is None and sym is None:
            continue
        sc = score_file_for(trace_path, p)
        if (best is None) or (sc > best_score):
            best = (conv, sym, p)
            best_score = sc
            # Early exit if we found both in same directory
            if sc[0] == 3 and conv is not None and sym is not None:
                break
    if best is None:
        return (None, None, None)
    return best

# read minimal census
rows = []
with open(census_in, 'r', encoding='utf-8') as f:
    rd = csv.reader(f, delimiter='\t')
    hdr = next(rd, None)
    for h in rd:
        rows.append({
            'hash': h[0],
            'confidence': h[1] or None,
            'tier': h[2],
            'source_path': h[3],
        })

# enrich
for r in rows:
    start = (root / r['source_path']).resolve()
    conv, sym, src = best_metrics_for_trace(start)
    r['convexity_deg'] = conv
    r['symmetry_rms']  = sym
    r['metrics_source']= str(src.relative_to(root)) if src else ''

# write full census
with open(census_out, 'w', encoding='utf-8', newline='') as f:
    wr = csv.writer(f, delimiter='\t')
    wr.writerow(['hash','convexity_deg','symmetry_rms','confidence','tier','source_path','metrics_source'])
    for r in rows:
        wr.writerow([r['hash'], r['convexity_deg'], r['symmetry_rms'], r['confidence'], r['tier'], r['source_path'], r['metrics_source']])

print('[enrich] wrote', census_out)
