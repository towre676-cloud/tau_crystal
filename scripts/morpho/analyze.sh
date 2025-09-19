#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
fr="$1"; lf="$2"; rf="$3"; out="$4"
[ -n "$fr" ] && [ -n "$lf" ] && [ -n "$rf" ] && [ -n "$out" ] || { echo "[analyze] usage: analyze.sh frontal left right out_dir"; exit 2; }
mkdir -p "$out" analysis/morpho/ledger analysis/morpho/thumbs
PY=python3; command -v "$PY" >/dev/null 2>&1 || PY=python
("$PY" -c "import numpy" ) >/dev/null 2>&1 || "$PY" -m pip install --user numpy >/dev/null 2>&1 || true
ENGINE="scripts/morpho/analyze_face.py"
[ -s "$ENGINE" ] || {
  : > "$ENGINE";
  printf "%s\n" "#!/usr/bin/env python3" >> "$ENGINE"
  printf "%s\n" "import json, math, csv, sys, os" >> "$ENGINE"
  printf "%s\n" "import numpy as np" >> "$ENGINE"
  printf "%s\n" "class Pt: __slots__=(\"x\",\"y\");" >> "$ENGINE"
  printf "%s\n" "def rd(p):" >> "$ENGINE"
  printf "%s\n" "  Q={};" >> "$ENGINE"
  printf "%s\n" "  with open(p,newline=\"\",encoding=\"utf-8\") as f:" >> "$ENGINE"
  printf "%s\n" "    r=csv.DictReader(f);"<< "$ENGINE" >/dev/null 2>&1 || true
  printf "%s\n" "    " >> "$ENGINE"
  printf "%s\n" "    [Q.setdefault(row[\"landmark\"], Pt()) for row in r]" >> "$ENGINE"
  printf "%s\n" "  R={k:Pt() for k in Q}" >> "$ENGINE"
  printf "%s\n" "  with open(p,newline=\"\",encoding=\"utf-8\") as f:" >> "$ENGINE"
  printf "%s\n" "    r=csv.DictReader(f);" >> "$ENGINE"
  printf "%s\n" "    for row in r:" >> "$ENGINE"
  printf "%s\n" "      try:" >> "$ENGINE"
  printf "%s\n" "        R[row[\"landmark\"]].x=float(row[\"x\"]); R[row[\"landmark\"]].y=float(row[\"y\"])" >> "$ENGINE"
  printf "%s\n" "      except: pass" >> "$ENGINE"
  printf "%s\n" "  return R" >> "$ENGINE"
  printf "%s\n" "def d(a,b): import math; return math.hypot(a.x-b.x,a.y-b.y)" >> "$ENGINE"
  printf "%s\n" "def ang(a,b,c):" >> "$ENGINE"
  printf "%s\n" "  import math; ux,uy=a.x-b.x,a.y-b.y; vx,vy=c.x-b.x,c.y-b.y" >> "$ENGINE"
  printf "%s\n" "  du=(ux*ux+uy*uy)**0.5; dv=(vx*vx+vy*vy)**0.5" >> "$ENGINE"
  printf "%s\n" "  if du==0 or dv==0: return float(\"nan\")" >> "$ENGINE"
  printf "%s\n" "  cs=(ux*vx+uy*vy)/(du*dv); cs=max(-1,min(1,cs)); return math.degrees(math.acos(cs))" >> "$ENGINE"
  printf "%s\n" "def refl_x(P,xb): return [type(\"Pt\",(),{\"x\":2*xb-p.x,\"y\":p.y})() for p in P]" >> "$ENGINE"
  printf "%s\n" "def procr(L,R):" >> "$ENGINE"
  printf "%s\n" "  X=np.array([[p.x,p.y] for p in L]); Y=np.array([[p.x,p.y] for p in R]); X-=X.mean(0); Y-=Y.mean(0)" >> "$ENGINE"
  printf "%s\n" "  U,S,Vt=np.linalg.svd(Y.T@X); Rm=U@Vt; " >> "$ENGINE"
  printf "%s\n" "  if np.linalg.det(Rm)<0: U[:,-1]*=-1; Rm=U@Vt" >> "$ENGINE"
  printf "%s\n" "  Yp=Y@Rm; den=np.trace(Yp.T@Yp); s=float(np.trace(Yp.T@X))/float(den) if den!=0 else 1.0" >> "$ENGINE"
  printf "%s\n" "  Rsd=X-(s*Yp); return float(((Rsd**2).sum()/X.size)**0.5)" >> "$ENGINE"
  printf %sn "def main():" >> "$ENGINE"
  printf "%s\n" "  fr,lf,rf,out=sys.argv[1:5]" >> "$ENGINE"
  printf "%s\n" "  F=rd(fr); L=rd(lf); R=rd(rf)" >> "$ENGINE"
  printf "%s\n" "  BZ=d(F[\"zy_l\"],F[\"zy_r\"]); FI=d(F[\"n\"],F[\"gn\"]) / BZ; UFI=d(F[\"n\"],F[\"sn\"]) / BZ; NI=d(F[\"al_l\"],F[\"al_r\"]) / d(F[\"n\"],F[\"sn\"]) " >> "$ENGINE"
  printf "%s\n" "  Lc=ang(L[\"g\"],L[\"sn\"],L[\"pg\"]); Rc=ang(R[\"g\"],R[\"sn\"],R[\"pg\"])" >> "$ENGINE"
  printf "%s\n" "  Ln=ang(L[\"prn\"],L[\"sn\"],L[\"ls\"]); Rn=ang(R[\"prn\"],R[\"sn\"],R[\"ls\"]) " >> "$ENGINE"
  printf "%s\n" "  xb=sum(F[k].x for k in [\"g\",\"n\",\"sn\",\"pg\"]) / 4.0" >> "$ENGINE"
  printf "%s\n" "  pairs=[(\"en_l\",\"en_r\"),(\"ex_l\",\"ex_r\"),(\"zy_l\",\"zy_r\"),(\"al_l\",\"al_r\"),(\"ch_l\",\"ch_r\")]" >> "$ENGINE"
  printf "%s\n" "  Lb=[F[a] for a,b in pairs]; Rb=[F[b] for a,b in pairs]" >> "$ENGINE"
  printf "%s\n" "  rms=procr(Lb, refl_x(Rb, xb)); asym=rms/BZ" >> "$ENGINE"
  printf "%s\n" "  outd={\"frontal\":{\"BZ\":BZ,\"FI\":FI,\"UFI\":UFI,\"NI\":NI},\"profiles\":{\"left\":{\"convexity_deg\":Lc,\"nasolabial_deg\":Ln},\"right\":{\"convexity_deg\":Rc,\"nasolabial_deg\":Rn},\"deltas\":{\"convexity_deg\":abs(Lc-Rc),\"nasolabial_deg\":abs(Ln-Rn)}},\"frontal_symmetry\":{\"procrustes_rms_px\":rms,\"asymmetry_dimless\":asym}}" >> "$ENGINE"
  printf "%s\n" "  os.makedirs(out,exist_ok=True);" >> "$ENGINE"
  printf "%s\n" "  with open(os.path.join(out,\"morpho_report.json\"),\"w\",encoding=\"utf-8\") as jf: json.dump(outd,jf,indent=2)" >> "$ENGINE"
  printf "%s\n" "  with open(os.path.join(out,\"morpho_report.md\"),\"w\",encoding=\"utf-8\") as mf: mf.write(str(outd))" >> "$ENGINE"
  printf "%s\n" "if __name__==\"__main__\": main()" >> "$ENGINE"
  chmod +x "$ENGINE"
}
"$PY" "$ENGINE" "analysis/morpho/input/frontal.csv" "analysis/morpho/input/left.csv" "analysis/morpho/input/right.csv" "$out" || {
  echo "[analyze] engine failed; verify landmark CSVs exist in analysis/morpho/input/"; exit 3;
}
if command -v magick >/dev/null 2>&1; then
  for f in "$fr" "$lf" "$rf"; do b="$(basename "$f")"; magick "$f" -resize 640x640 -blur 0x2 "analysis/morpho/thumbs/${b%.*}_thumb.jpg" || true; done
fi
ts="$(date -u +%Y-%m-%dT%H:%M:%SZ)"
L="analysis/morpho/ledger/morpho_ci.jsonl"; [ -f "$L" ] || : > "$L"
sha(){ openssl dgst -sha256 "$1" | awk "{print \$2}"; }
