import os, csv, sys

# Choose first existing input among your known filenames
cands = [
  'tsv/elliptic_q1_fourier_sane_bps.tsv',
  'tsv/elliptic_q1_fourier_bps.tsv',
  'tsv/elliptic_q1_fourier.tsv',
  'tsv/elliptic_q1.tsv'
]
inp = next((p for p in cands if os.path.exists(p)), None)
if not inp:
    sys.exit(0)  # nothing to do yet

outp = 'tsv/elliptic_q1_charge_resolved.tsv'

# Column helpers
def pick(d, *keys):
    for k in keys:
        if k in d: return d[k]
    lk = {k.lower(): k for k in d}
    for k in keys:
        if k.lower() in lk: return d[lk[k.lower()]]
    return None

rows = []
with open(inp, 'r', newline='') as f:
    rdr = csv.DictReader(f, delimiter='\t')
    for d in rdr:
        rs = pick(d, 'r','k','exp','power','m','charge')
        Re = pick(d, 'Re','real','re','Re_unproj')
        Im = pick(d, 'Im','imag','im','Im_unproj')
        try:
            r = int(str(rs).strip())
            cre = float(str(Re).strip())
            cim = float(str(Im).strip())
        except Exception:
            continue
        rows.append((r, complex(cre, cim)))

if not rows:
    sys.exit(0)

rows.sort(key=lambda t: t[0])
absmap = {r: abs(c) for r, c in rows}

# Pick symmetry shift K by minimizing mean | |c_r| - |c_{r+K}| |
best = (1e99, 0)
for K in range(-12, 13):
    if K == 0: continue
    pairs = [(absmap[r], absmap[r+K]) for r in absmap if (r+K) in absmap]
    if not pairs: continue
    mean = sum(abs(a-b) for a,b in pairs)/len(pairs)
    if mean < best[0]: best = (mean, K)
K = best[1]

with open(outp, 'w', newline='') as g:
    w = csv.writer(g, delimiter='\t')
    w.writerow(['r','Re_unproj','Im_unproj','Abs_unproj','partner_r','Abs_partner','Abs_proj_avg','Rel_sym_resid'])
    for r, c in rows:
        partner = r + K
        a = abs(c)
        cp = absmap.get(partner, 0.0)
        avg = 0.5*(a+cp) if partner in absmap else a
        resid = (a-avg)/(avg if avg else 1.0)
        w.writerow([r, c.real, c.imag, a, partner if partner in absmap else '', cp if partner in absmap else '', avg, resid])
