import csv, sys, os, cmath

A   = 'tsv/elliptic_q1_fourier_sane_bps.tsv'
B   = 'tsv/elliptic_q1_fourier_sane_bps_tauB.tsv'
OUT = 'tsv/elliptic_q1_fourier_sane_bps_tauB_aligned.tsv'

def sniff(path):
    with open(path,'r',encoding='utf-8',errors='replace',newline='') as f:
        s=f.read(4096)
    return '\t' if s.count('\t')>=s.count(',') else ','

def pick(d,*keys):
    for k in keys:
        if k in d: return d[k]
    L={k.lower():k for k in d}
    for k in keys:
        if k.lower() in L: return d[L[k.lower()]]
    return None

R_KEYS  = ('r','k','exp','power','m','charge','R','m_idx')
RE_KEYS = ('Re','real','re','Re_unproj','Re_bps','ReBPS','Re_scaled','Real','Re_c_r_BPS','Re_c_r','Re_c')
IM_KEYS = ('Im','imag','im','Im_unproj','Im_bps','ImBPS','Im_scaled','Imag','Im_c_r_BPS','Im_c_r','Im_c')

def load(path):
    D={}
    delim=sniff(path)
    with open(path,'r',encoding='utf-8',errors='replace',newline='') as f:
        rdr=csv.DictReader(f, delimiter=delim)
        for row in rdr:
            try:
                r  = int((pick(row,*R_KEYS) or '').strip())
                Re = float((pick(row,*RE_KEYS) or '').strip())
                Im = float((pick(row,*IM_KEYS) or '').strip())
                D[r] = complex(Re,Im)
            except Exception:
                continue
    return D, delim, rdr.fieldnames if 'rdr' in locals() else None

DA, delimA, hdrA = load(A)
DB, delimB, hdrB = load(B)

if not DA or not DB:
    print("[align] missing or empty A/B; abort")
    sys.exit(1)

R = sorted(set(DA) & set(DB))
if not R:
    print("[align] no overlapping charges; abort")
    sys.exit(1)

# λ = (Σ_r conj(B_r)*A_r) / (Σ_r |B_r|^2)
num = sum(DB[r].conjugate()*DA[r] for r in R)
den = sum(abs(DB[r])**2 for r in R)
lam = num/den if den!=0 else 0j

# residuals before/after
res0 = sum(abs(DA[r]-DB[r]) for r in R)/max(1,len(R))
res1 = sum(abs(DA[r]-lam*DB[r]) for r in R)/max(1,len(R))

print(f"[align] lambda = {lam.real:.6e} + {lam.imag:.6e}i  |lam|={abs(lam):.6e}  arg={cmath.phase(lam):.6f} rad")
print(f"[align] mean abs residual: before={res0:.3e}  after={res1:.3e}")

# write aligned B with same headers if possible (prefer preserving input B headers)
# if B header had 'Re_c_r_BPS'/'Im_c_r_BPS', keep them
hdr = hdrB if hdrB else ['r','Re_c_r_BPS','Im_c_r_BPS']
use_re, use_im = None, None
if hdrB:
    # pick first matching header names to write back into
    for k in RE_KEYS:
        if k in hdrB: use_re = k; break
    for k in IM_KEYS:
        if k in hdrB: use_im = k; break
if not use_re: use_re='Re_c_r_BPS'
if not use_im: use_im='Im_c_r_BPS'

# Load B rows verbatim and scale numeric rows
rows=[]
with open(B,'r',encoding='utf-8',errors='replace',newline='') as f:
    rdr=csv.DictReader(f, delimiter=delimB)
    hdr = rdr.fieldnames
    for row in rdr:
        try:
            r = int((pick(row,*R_KEYS) or '').strip())
            z = DB.get(r)
            if z is None: 
                rows.append(row); 
                continue
            z2 = lam*z
            row[use_re] = f"{z2.real:.16g}"
            row[use_im] = f"{z2.imag:.16g}"
            rows.append(row)
        except Exception:
            rows.append(row)

with open(OUT,'w',encoding='utf-8',newline='') as g:
    w=csv.DictWriter(g, fieldnames=hdr, delimiter=delimB)
    w.writeheader(); w.writerows(rows)

print(f"[align] wrote aligned: {OUT}")
sys.exit(0)
