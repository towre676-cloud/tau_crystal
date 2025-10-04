#!/usr/bin/env python3
import sys, os, csv, datetime as dt
try:
    import matplotlib.pyplot as plt
except Exception as e:
    print(f"[plot] matplotlib unavailable: {e}")
    sys.exit(0)
LEDGER_DIR = os.environ.get('LEDGER_DIR', '.tau_ledger')
hist = os.path.join(LEDGER_DIR, 'BUDGET_history.tsv')
if not os.path.isfile(hist):
    print('[plot] no history file; nothing to plot')
    sys.exit(0)
ts, vals = [], []
with open(hist, 'r', newline='') as fh:
    rdr = csv.reader(fh, delimiter='\t')
    header = next(rdr, None)
    for row in rdr:
        if len(row) != 2: continue
        try:
            t = dt.datetime.strptime(row[0], '%Y%m%dT%H%M%SZ')
            v = float(row[1])
        except Exception:
            continue
        ts.append(t)
        vals.append(v)
if not ts:
    print('[plot] history empty; nothing to plot')
    sys.exit(0)
plt.figure()
plt.plot(ts, vals, marker='o')
plt.xlabel('UTC time')
plt.ylabel('curvature_sum')
plt.title('τ‑Crystal Curvature Budget History')
plt.grid(True)
png = os.path.join(LEDGER_DIR, 'budget_history.png')
svg = os.path.join(LEDGER_DIR, 'budget_history.svg')
try:
    plt.savefig(png, dpi=160, bbox_inches='tight')
    plt.savefig(svg, bbox_inches='tight')
    print(f'[plot] wrote {png} and {svg}')
except Exception as e:
    print(f'[plot] save failed: {e}')
sys.exit(0)
