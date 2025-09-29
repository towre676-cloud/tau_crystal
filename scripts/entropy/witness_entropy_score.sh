cd "$HOME/Desktop/tau_crystal/tau_crystal" || exit 1
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
dir=".tau_ledger/entropy"; mkdir -p "$dir"
out="$dir/witness_scores.csv"; : > "$out"; printf "%s\n" "file,bytes,sha256,k_est" >> "$out"
for f in "$dir"/witness_*.json; do [ -f "$f" ] || continue; b=$(wc -c <"$f" | tr -d "[:space:]"); h=$(openssl dgst -sha256 "$f" | awk "{print \$2}");
  k=$(python - <<PY\nimport sys,json\np=sys.argv[1]\ns=open(p,"rb").read()\n# crude compression proxy: distinct byte ratio with log scaling\nfrom collections import Counter\nc=Counter(s)\nH=-sum((v/len(s))*(__import__("math").log(v/len(s)+1e-12) ) for v in c.values())\nprint(f"{H:.4f}")\nPY\n "$f"); printf "%s\n" "$(basename "$f"),$b,$h,$k" >> "$out"; done
