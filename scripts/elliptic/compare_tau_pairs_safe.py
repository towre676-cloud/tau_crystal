import csv, sys, os, statistics

A   = 'tsv/elliptic_q1_fourier_sane_bps.tsv'
B   = 'tsv/elliptic_q1_fourier_sane_bps_tauB.tsv'
OUT = 'tsv/elliptic_q1_conditioning_audit.tsv'
SUM = 'tsv/elliptic_q1_conditioning_summary.txt'

def sniff_delim(path):
    with open(path,'r',encoding='utf-8',errors='replace',newline='') as f:
        s=f.read(4096)
    return '\t' if s.count('\t')>=s.count(',') else ','

def pick(d, *keys):
    for k in keys:
        if k in d: return d[k]
    lower={k.lower():k for k in d}
    for k in keys:
        kk=k.lower()
        if kk in lower: return d[lower[kk]]
    return None

# include your header variants explicitly
RE_KEYS = ('Re','real','re','Re_unproj','Re_bps','ReBPS','Re_scaled','ReRaw','Real','Re_c_r_BPS','Re_c_r','Re_c')
IM_KEYS = ('Im','imag','im','Im_unproj','Im_bps','ImBPS','Im_scaled','ImRaw','Imag','Im_c_r_BPS','Im_c_r','Im_c')
R_KEYS  = ('r','k','exp','power','m','charge','R','m_idx')

def load(path):
    if not os.path.exists(path): return None
    D={}
    delim=sniff_delim(path)
    with open(path,'r',encoding='utf-8',errors='replace',newline='') as f:
        rdr=csv.DictReader(f, delimiter=delim)
        for row in rdr:
            try:
                r  = int((pick(row,*R_KEYS) or '').strip())
                Re = float((pick(row,*RE_KEYS) or '').strip())
                Im = float((pick(row,*IM_KEYS) or '').strip())
            except Exception:
                continue
            D[r]=(Re,Im)
    return D if D else {}

def write_skip(msg):
    with open(SUM,'w',encoding='utf-8') as g: g.write(msg+"\n")

DA=load(A); DB=load(B)
if DA is None: write_skip(f"[skip] primary file missing: {A}"); sys.exit(0)
if DB is None: write_skip(f"[skip] second tau-pair file missing: {B}"); sys.exit(0)
if not DA:     write_skip(f"[skip] primary file present but no parseable rows: {A}"); sys.exit(0)
if not DB:     write_skip(f"[skip] second tau-pair file present but no parseable rows: {B}"); sys.exit(0)

rs=sorted(set(DA)&set(DB))
if not rs:
    write_skip("[warn] no overlapping charge indices between A and B"); sys.exit(0)

rows=[]; reldiffs=[]
for r in rs:
    a=complex(*DA[r]); b=complex(*DB[r]); d=b-a
    rel=abs(d)/max(abs(a),abs(b),1.0)
    rows.append([r,a.real,a.imag,b.real,b.imag,d.real,d.imag,rel])
    reldiffs.append(rel)

with open(OUT,'w',encoding='utf-8',newline='') as g:
    w=csv.writer(g, delimiter='\t')
    w.writerow(['r','Re_A','Im_A','Re_B','Im_B','dRe','dIm','rel_abs_diff'])
    w.writerows(rows)

p50=statistics.median(reldiffs)
p90=(statistics.quantiles(reldiffs,n=10)[8] if len(reldiffs)>=10 else max(reldiffs))
with open(SUM,'w',encoding='utf-8') as g:
    g.write("conditioning audit\n")
    g.write(f"pairs compared: {len(rs)}\n")
    g.write(f"median rel_abs_diff: {p50:.3e}\n")
    g.write(f"P90    rel_abs_diff: {p90:.3e}\n")
    g.write(f"OUT: {OUT}\n")
