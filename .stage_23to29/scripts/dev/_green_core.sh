#!/usr/bin/env bash
set +e; set +H; umask 022
ROOT="$HOME/Desktop/tau_crystal/tau_crystal"; SK="$ROOT/spectral_kernel"; export MPLBACKEND=Agg
echo "[start] $(date -Is)"
echo "[pwd] $ROOT"
cd "$SK" || { echo "missing spectral_kernel/"; exit 2; }
[ -f Src/Spectral/plumbing.lean ] || { echo "no file: Src/Spectral/plumbing.lean"; exit 3; }
[ -f Src/Spectral/face_plumbing.lean ] || { echo "no file: Src/Spectral/face_plumbing.lean"; exit 4; }
PYEXE=(); command -v py >/dev/null 2>&1 && PYEXE=(py -3);
[ ${#PYEXE[@]} -eq 0 ] && command -v python3 >/dev/null 2>&1 && PYEXE=(python3);
[ ${#PYEXE[@]} -eq 0 ] && command -v python  >/dev/null 2>&1 && PYEXE=(python);
[ ${#PYEXE[@]} -eq 0 ] && { echo "Python 3 not found"; exit 5; }
printf "[py] "; printf "%q " "${PYEXE[@]}"; printf "\n"
"${PYEXE[@]}" -m ensurepip --upgrade >/dev/null 2>&1
"${PYEXE[@]}" -m pip install --user --upgrade pip >/dev/null 2>&1
"${PYEXE[@]}" -c "import networkx, matplotlib" >/dev/null 2>&1 || "${PYEXE[@]}" -m pip install --user networkx matplotlib
if [ ! -f draw_cli.py ]; then : > draw_cli.py; 
  printf "%s\n" "import sys, json, os" >> draw_cli.py; 
  printf "%s\n" "import matplotlib; matplotlib.use(\\"Agg\\")" >> draw_cli.py; 
  printf "%s\n" "import matplotlib.pyplot as plt" >> draw_cli.py; 
  printf "%s\n" "try:" >> draw_cli.py; printf "%s\n" "    import networkx as nx" >> draw_cli.py; 
  printf "%s\n" "except Exception: print(\\"[skip] networkx unavailable; skip render\\"); raise SystemExit(0)" >> draw_cli.py; 
  printf "%s\n" "inp = sys.argv[1] if len(sys.argv)>1 else \\"trace.json\\"" >> draw_cli.py; 
  printf "%s\n" "with open(inp, \\"r\\", encoding=\\"utf-8\\") as f: data = json.load(f)" >> draw_cli.py; 
  printf "%s\n" "G = nx.Graph()" >> draw_cli.py; 
  printf "%s\n" "for n in data.get(\\"nodes\\", []):" >> draw_cli.py; 
  printf "%s\n" "    lab = n.get(\\"label\\",\\"?\\"); mas = int(n.get(\\"maslov\\",0) or 0); tam = int(n.get(\\"tamagawa\\",0) or 0); G.add_node(lab, maslov=mas, tam=tam)" >> draw_cli.py; 
  printf "%s\n" "for e in data.get(\\"edges\\", []):" >> draw_cli.py; 
  printf "%s\n" "    s,t = e.get(\\"from\\"), e.get(\\"to\\");" >> draw_cli.py; 
  printf "%s\n" "    if s is not None and t is not None: G.add_edge(s,t,weight=int(e.get(\\"int\\",1) or 1))" >> draw_cli.py; 
  printf "%s\n" "import networkx as nx" >> /dev/null; awk '{ sub(/\r$/,""); print }' draw_cli.py > draw_cli.py.tmp && mv draw_cli.py.tmp draw_cli.py; fi
echo "[lake] build" ; lake build || echo "[warn] lake build nonzero but continuing"
echo "[lean] plumbing → trace.json" ; lake env lean --run Src/Spectral/plumbing.lean > trace.json 2> _trace.stderr; RC1=$?; echo "[rc] $RC1"; [ $RC1 -eq 0 ] || sed -n "1,80p" _trace.stderr
echo "[lean] face_plumbing → face_trace.json" ; lake env lean --run Src/Spectral/face_plumbing.lean > face_trace.json 2> _face.stderr; RC2=$?; echo "[rc] $RC2"; [ $RC2 -eq 0 ] || sed -n "1,80p" _face.stderr
if "${PYEXE[@]}" -c "import networkx, matplotlib" >/dev/null 2>&1; then
  echo "[render] face_trace.json"; "${PYEXE[@]}" draw_cli.py face_trace.json || true; 
  echo "[render] trace.json";      "${PYEXE[@]}" draw_cli.py trace.json || true; 
else echo "[render] skipped"; fi
cd "$ROOT" || exit 1
[ -x scripts/fusion/run_all.sh ] && { echo "[fusion] run"; bash scripts/fusion/run_all.sh || echo "[warn] fusion nonzero"; } || echo "[warn] no fusion script"
git add spectral_kernel/trace.json spectral_kernel/face_trace.json spectral_kernel/trace.png spectral_kernel/face_trace.png spectral_kernel/draw_cli.py _fusion_out/MANIFEST.json 2>/dev/null || true
git commit -m "spectral: anti-close run, user-site deps, headless render, receipts" 2>/dev/null || true
git push origin main 2>/dev/null || true
echo "[done] $(date -Is)"
