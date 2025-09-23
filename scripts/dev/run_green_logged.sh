#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
shopt -s expand_aliases
PS4="+ [$(date +%H:%M:%S)] ${BASH_SOURCE##*/}:${LINENO}: "
set -o errtrace
set -x
ROOT="$HOME/Desktop/tau_crystal/tau_crystal"
SK="$ROOT/spectral_kernel"
LOGDIR="$ROOT/.tau_ledger/logs"
TS=$(date +%Y%m%d_%H%M%S)
LOG="$LOGDIR/fusion_${TS}.log"
mkdir -p "$LOGDIR"
exec > >(tee -a "$LOG") 2>&1
trap 'code=$?; set +x; echo ""; echo "[FAIL] exit $code · log: $LOG"; echo "---- tail ----"; tail -n 300 "$LOG" || true; exit $code' ERR
echo "[start] $(date -Is) · log: $LOG"
export MPLBACKEND=Agg
echo "[pwd] $PWD"; ls -la
[ -d "$SK" ] || { echo "missing dir: spectral_kernel/"; exit 1; }
cd "$SK"; echo "[pwd] $PWD"; ls -la
[ -f Src/Spectral/plumbing.lean ] || { echo "no file: Src/Spectral/plumbing.lean"; exit 1; }
[ -f Src/Spectral/face_plumbing.lean ] || { echo "no file: Src/Spectral/face_plumbing.lean"; exit 1; }
command -v lake >/dev/null 2>&1 || { echo "lake not found in PATH"; exit 1; }
lake --version || true
PYEXE=()
if command -v py >/dev/null 2>&1; then PYEXE=(py -3); fi
if [ ${#PYEXE[@]} -eq 0 ] && command -v python3 >/dev/null 2>&1; then PYEXE=(python3); fi
if [ ${#PYEXE[@]} -eq 0 ] && command -v python  >/dev/null 2>&1; then PYEXE=(python); fi
[ ${#PYEXE[@]} -ne 0 ] || { echo "Python 3 not found. Install 3.10+."; exit 1; }
printf "[py] using: "; printf "%q " "${PYEXE[@]}"; printf "\n"
"${PYEXE[@]}" -m ensurepip --upgrade >/dev/null 2>&1 || true
"${PYEXE[@]}" -m pip install --user --upgrade pip >/dev/null 2>&1 || true
if ! "${PYEXE[@]}" -c "import networkx, matplotlib" >/dev/null 2>&1; then "${PYEXE[@]}" -m pip install --user networkx matplotlib; fi
"${PYEXE[@]}" - <<PY || true
import sys, networkx, matplotlib; print("[py ok] networkx", networkx.__version__, "matplotlib", matplotlib.__version__)
PY
if [ ! -f draw_cli.py ]; then
  : > draw_cli.py
  printf "%s\n" "import sys, json, os" >> draw_cli.py
  printf "%s\n" "import matplotlib; matplotlib.use(\\"Agg\\")" >> draw_cli.py
  printf "%s\n" "import matplotlib.pyplot as plt" >> draw_cli.py
  printf "%s\n" "try:" >> draw_cli.py
  printf "%s\n" "    import networkx as nx" >> draw_cli.py
  printf "%s\n" "except Exception:" >> draw_cli.py
  printf "%s\n" "    print(\\"[skip] networkx unavailable; skip render\\"); raise SystemExit(0)" >> draw_cli.py
  printf "%s\n" "inp = sys.argv[1] if len(sys.argv)>1 else \\"trace.json\\"" >> draw_cli.py
  printf "%s\n" "with open(inp, \\"r\\", encoding=\\"utf-8\\") as f: data = json.load(f)" >> draw_cli.py
  printf "%s\n" "G = nx.Graph()" >> draw_cli.py
  printf "%s\n" "for n in data.get(\\"nodes\\", []):" >> draw_cli.py
  printf "%s\n" "    lab = n.get(\\"label\\",\\"?\\")" >> draw_cli.py
  printf "%s\n" "    mas = int(n.get(\\"maslov\\",0) or 0)" >> draw_cli.py
  printf "%s\n" "    tam = int(n.get(\\"tamagawa\\",0) or 0)" >> draw_cli.py
  printf "%s\n" "    G.add_node(lab, maslov=mas, tam=tam)" >> draw_cli.py
  printf "%s\n" "for e in data.get(\\"edges\\", []):" >> draw_cli.py
  printf "%s\n" "    s,t = e.get(\\"from\\"), e.get(\\"to\\")" >> draw_cli.py
  printf "%s\n" "    if s is not None and t is not None:" >> draw_cli.py
  printf "%s\n" "        w = int(e.get(\\"int\\",1) or 1)" >> draw_cli.py
  printf "%s\n" "        G.add_edge(s,t,weight=w)" >> draw_cli.py
  printf "%s\n" "if len(G)==0: print(\\"empty graph; nothing to draw\\"); raise SystemExit(0)" >> draw_cli.py
  printf "%s\n" "pos = nx.spring_layout(G, seed=1)" >> draw_cli.py
  printf "%s\n" "colors = [\\"green\\" if G.nodes[v][\\"maslov\\"]==1 else \\"red\\" for v in G]" >> draw_cli.py
  printf "%s\n" "labels = {v: f\\"{v}\\n{G.nodes[v][\\"tam\\"]}\\" for v in G}" >> draw_cli.py
  printf "%s\n" "plt.figure(figsize=(6,4), dpi=140)" >> draw_cli.py
  printf "%s\n" "nx.draw(G, pos, node_color=colors, with_labels=False)" >> draw_cli.py
  printf "%s\n" "nx.draw_networkx_labels(G, pos, labels=labels, font_size=7)" >> draw_cli.py
  printf "%s\n" "out = os.path.splitext(os.path.basename(inp))[0] + \\".png\\"" >> draw_cli.py
  printf "%s\n" "plt.savefig(out, bbox_inches=\\"tight\\")" >> draw_cli.py
  printf "%s\n" "print(f\\"[ok] wrote {out}\\")" >> draw_cli.py
  awk '{ sub(/\r$/,""); print }' draw_cli.py > draw_cli.py.tmp && mv draw_cli.py.tmp draw_cli.py
fi
echo "[step] lake build"
lake build
echo "[step] emit trace.json"
set +e; lake env lean --run Src/Spectral/plumbing.lean > trace.json 2> _trace.stderr; rc=$?; set -e; echo "[lean plumbing rc=$rc]"; [ $rc -eq 0 ] || cat _trace.stderr
echo "[step] emit face_trace.json"
set +e; lake env lean --run Src/Spectral/face_plumbing.lean > face_trace.json 2> _face.stderr; rc=$?; set -e; echo "[lean face_plumbing rc=$rc]"; [ $rc -eq 0 ] || cat _face.stderr
if "${PYEXE[@]}" -c "import networkx, matplotlib" >/dev/null 2>&1; then
  echo "[step] render face_trace.png" ; "${PYEXE[@]}" draw_cli.py face_trace.json || true
  echo "[step] render trace.png"      ; "${PYEXE[@]}" draw_cli.py trace.json || true
else
  echo "[render] skipping local render; CI will render on Ubuntu."
fi
cd "$ROOT"; echo "[pwd] $PWD"
[ -x scripts/fusion/run_all.sh ] || { echo "missing scripts/fusion/run_all.sh"; exit 1; }
echo "[step] fusion"; bash scripts/fusion/run_all.sh
echo "[step] git add/commit/push"
git add spectral_kernel/trace.json spectral_kernel/face_trace.json spectral_kernel/trace.png spectral_kernel/face_trace.png spectral_kernel/draw_cli.py _fusion_out/MANIFEST.json || true
git commit -m "spectral: traced run, user-site deps, headless render, fresh receipts" || true
git push origin main
set +x; echo "[done] $(date -Is) · log: $LOG"
