#!/usr/bin/env bash
set +H; set -euo pipefail
DATA_ROOT=${1:-"/c/Users/Cody/Downloads/LS3D-W/LS3D-W"}
OUTDIR="analysis/geom"; CAN="$OUTDIR/canonical"; SYM="$OUTDIR/symmetry.tsv"; STAB="$OUTDIR/stability.tsv"; ANC="$OUTDIR/anchors.tsv"; BIN="$OUTDIR/binary.tsv"
mkdir -p "$OUTDIR" "$CAN"
REC_CAN="$OUTDIR/canonical.receipt.tsv"; : > "$REC_CAN"; : > "$SYM"; : > "$STAB"; : > "$ANC"; : > "$BIN"
find "$DATA_ROOT" -type f -name "*.mat" -print0 | while IFS= read -r -d "" F; do
  python3 scripts/geom/canonicalize.py "$F" "$CAN" "$REC_CAN"
done
for NPY in "$CAN"/*.canon.npy; do
  [ -f "$NPY" ] || continue
  python3 scripts/geom/check_symmetry.py "$NPY" "$SYM"
  python3 scripts/geom/binary_inference.py "$NPY" "$BIN"
done
python3 scripts/geom/find_anchors.py "$SYM" 0.02 "$ANC"
exit 0
