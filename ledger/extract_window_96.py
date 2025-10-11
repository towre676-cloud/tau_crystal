import json, numpy as np, csv, sys
from pathlib import Path
src, outdir = Path(sys.argv[1]), Path(sys.argv[2]); outdir.mkdir(parents=True, exist_ok=True)
data = json.loads(Path(src).read_text())
modes = [m for m in data['modes'] if m['k_class']=='chiral' and m['weight']=='surviving'][:96]
A = np.array([m['A_row'] for m in modes],float)
B = np.array([m['B_row'] for m in modes],float)
np.savetxt(outdir/'A.csv',A,delimiter=',')
np.savetxt(outdir/'B.csv',B,delimiter=',')
# sector map and neutral bases come from the same JSON, if present
if 'sector_map' in data: Path(outdir/'splits.json').write_text(json.dumps(data['sector_map'],indent=2))
if 'neutral_A' in data and 'neutral_B' in data:
    np.savetxt(outdir/'neutral_A.csv',np.array(data['neutral_A'],float),delimiter=',')
    np.savetxt(outdir/'neutral_B.csv',np.array(data['neutral_B'],float),delimiter=',')
