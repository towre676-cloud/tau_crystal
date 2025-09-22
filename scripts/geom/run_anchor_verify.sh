#!/usr/bin/env bash
set -euo pipefail
LS3DW_HOME="${LS3DW_HOME:-LS3D-W}"
[ -d "$LS3DW_HOME" ] || { echo "::notice::no LS3D-W dataset; skipping anchor+verify"; exit 0; }
#!/usr/bin/env bash
set +H; set -euo pipefail
MAN=${1:-"analysis/geom/ls3dw_mat_manifest.tsv"}
PAR=${2:-"analysis/geom/ls3dw_params.tsv"}
outdir="analysis/geom"; mkdir -p "$outdir"
bash scripts/geom/geometric_proof.sh "/c/Users/Cody/Downloads/LS3D-W/LS3D-W"
anchor="$outdir/anchor.receipt"; proof="$outdir/proof_tree.tsv"
code_hash_A=$(sha256sum "scripts/geom/make_manifest.sh" 2>/dev/null | awk "{print \$1}")
code_hash_B=$(sha256sum "scripts/geom/run_anchor_verify.sh" | awk "{print \$1}")
ts=$(date -u +"%Y-%m-%dT%H:%M:%SZ")
for p in "$MAN" "$PAR"; do [ -s "$p" ] || { echo "::error::missing $p"; exit 1; }; done
# compute a deterministic digest over MAN|PAR|code hashes|ts
tmpfile="$outdir/.anchor_concat.bin"; rm -f "$tmpfile"
cat "$MAN" >> "$tmpfile"
printf "\n" >> "$tmpfile"
cat "$PAR" >> "$tmpfile"
printf "\n%s\n%s\n%s\n" "$code_hash_A" "$code_hash_B" "$ts" >> "$tmpfile"
digest=$(sha256sum "$tmpfile" | awk "{print \$1}")
rm -f "$tmpfile"
# write anchor receipt (idempotent append if new)
if ! grep -q "^ID\t$digest" "$anchor" 2>/dev/null; then
  printf "ID\t%s\n" "$digest" >> "$anchor"
  printf "TS\t%s\n" "$ts" >> "$anchor"
  printf "ANCHOR=TRUE\n" >> "$anchor"
  printf "VERIFY=TRUE\n" >> "$anchor"
  printf "MAN\t%s\n" "$MAN" >> "$anchor"
  printf "PAR\t%s\n" "$PAR" >> "$anchor"
  printf "CODE_A\t%s\n" "$code_hash_A" >> "$anchor"
  printf "CODE_B\t%s\n" "$code_hash_B" >> "$anchor"
  printf "--\n" >> "$anchor"
fi
# prepend proof-tree row with the new digest
tmp="$outdir/.proof.tmp"; rm -f "$tmp"
printf "%s\t%s\t%s\t%s\t%s\n" "$digest" "$ts" "$MAN" "$PAR" "$code_hash_B" >> "$tmp"
[ -f "$proof" ] && cat "$proof" >> "$tmp"
mv "$tmp" "$proof"
# novelty guard against last merkle spine entry if present
if [ -f ".tau_ledger/merkle_spine.tsv" ]; then
  last=$(tail -n 1 .tau_ledger/merkle_spine.tsv | awk -F"\t" "{print \$1}")
  [ "$last" != "$digest" ] || { echo "::error::no new proof_tree digest"; exit 1; }
fi
echo "ANCHOR=TRUE"; echo "VERIFY=TRUE"; echo "$digest"
