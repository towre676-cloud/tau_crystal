#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C

REPO="${1:-.}"                 # repo root
BRANCH="${2:-}"                # optional target branch
TARGET_DIR="monographs/dlr-bordisms"
STAMP="$(date -u +%Y%m%dT%H%M%SZ)"

mkdir -p "$REPO"; cd "$REPO"

# init git if needed
if [ ! -d .git ]; then
  git init -q
  git config --local user.name  "tau-crystal-bot" || true
  git config --local user.email "bot@local" || true
fi

# optional: checkout/create branch
if [ -n "$BRANCH" ]; then
  if git rev-parse --verify "$BRANCH" >/dev/null 2>&1; then
    git checkout -q "$BRANCH"
  else
    git checkout -q -b "$BRANCH"
  fi
fi

mkdir -p "$TARGET_DIR"

RAW="$TARGET_DIR/.raw_$STAMP.txt"
cat > "$RAW"   # read manuscript from stdin

# hard fail if empty
[ -s "$RAW" ] || { echo "[err] no manuscript on stdin"; exit 1; }

# strip CRs, keep verbatim content otherwise
tr -d '\r' < "$RAW" > "$RAW.clean" && mv "$RAW.clean" "$RAW"

# find line numbers for section headers
# (we anchor on your exact text; if you rename headers, update the regexes)
getln() { grep -n -m1 -F "$1" "$RAW" | cut -d: -f1 || true; }

L_START=1
L_ABS=$(getln "Abstract")
L_INTRO=$(getln "Introduction")
L_DET=$(getln "Determinant Lines and Zeta-Regularized Residues")
L_TAU=$(getln "The τ-Coordinate and Berry-Quillen Holonomy")
[ -z "$L_TAU" ] && L_TAU=$(getln "The t-Coordinate and Berry-Quillen Holonomy") || true  # safety
L_ENT=$(getln "Entropy as Curvature of a Local System")
L_WIT=$(getln "The Witness Cosheaf and Semantic Drift")
L_ANO=$(getln "Anomaly Theory and the Universal Determinant Gerbe")
L_OPS=$(getln "Operator Theory for Numerical Pipelines")
L_IMP=$(getln "Implementation and Receipt Format")
L_ZK=$(getln "Zero-Knowledge Extensions and Enclave Computing")
L_PRED=$(getln "Predictive Holonomy and \"Looking Around Corners\"")
L_COMP=$(getln "Comparison with Existing Approaches and Related Work")
L_CONC=$(getln "Conclusion")
L_ACK=$(getln "Acknowledgments")
L_APP=$(getln "Appendix: Explicit Formulas for Toy Models")
L_END=$(wc -l < "$RAW" | tr -d ' ')

# quick guardrails
need=( "$L_ABS" "$L_INTRO" "$L_DET" "$L_TAU" "$L_ENT" "$L_WIT" "$L_ANO" "$L_OPS" "$L_IMP" "$L_ZK" "$L_PRED" "$L_COMP" "$L_CONC" "$L_ACK" "$L_APP" )
for v in "${need[@]}"; do
  [ -n "$v" ] || { echo "[err] could not detect all expected headers. aborting."; exit 1; }
done

# helper to extract lines [a..b] into a file
slice() {
  local a="$1" b="$2" out="$3"
  [ "$a" -le "$b" ] || { : > "$out"; return 0; }
  sed -n "${a},${b}p" "$RAW" > "$out"
}

# write 12 contiguous, verbatim chunks (grouping multiple sections where needed)
declare -a FILES TITLES RANGES

# 01: Title + Abstract (start -> line before "Introduction")
FILES+=( "01-title-and-abstract.md" )
TITLES+=( "Title + Abstract" )
RANGES+=( "$L_START:$((L_INTRO-1))" )

# 02: Introduction
FILES+=( "02-introduction.md" )
TITLES+=( "Introduction" )
RANGES+=( "$L_INTRO:$((L_DET-1))" )

# 03: Determinant Lines (full)
FILES+=( "03-determinant-lines.md" )
TITLES+=( "Determinant Lines and Zeta-Regularized Residues" )
RANGES+=( "$L_DET:$((L_TAU-1))" )

# 04: τ-Coordinate (full)
FILES+=( "04-tau-coordinate.md" )
TITLES+=( "The τ-Coordinate and Berry-Quillen Holonomy" )
RANGES+=( "$L_TAU:$((L_ENT-1))" )

# 05: Entropy (part 1) — from ENTROPY start to just before Witness Cosheaf
FILES+=( "05-entropy-local-system.md" )
TITLES+=( "Entropy as Curvature of a Local System" )
RANGES+=( "$L_ENT:$((L_WIT-1))" )

# 06: Witness Cosheaf
FILES+=( "06-witness-cosheaf.md" )
TITLES+=( "The Witness Cosheaf and Semantic Drift" )
RANGES+=( "$L_WIT:$((L_ANO-1))" )

# 07: Anomaly Theory
FILES+=( "07-anomaly-theory.md" )
TITLES+=( "Anomaly Theory and the Universal Determinant Gerbe" )
RANGES+=( "$L_ANO:$((L_OPS-1))" )

# 08: Operator Theory
FILES+=( "08-operator-theory.md" )
TITLES+=( "Operator Theory for Numerical Pipelines" )
RANGES+=( "$L_OPS:$((L_IMP-1))" )

# 09: Implementation
FILES+=( "09-implementation.md" )
TITLES+=( "Implementation and Receipt Format" )
RANGES+=( "$L_IMP:$((L_ZK-1))" )

# 10: Zero-Knowledge
FILES+=( "10-zero-knowledge.md" )
TITLES+=( "Zero-Knowledge Extensions and Enclave Computing" )
RANGES+=( "$L_ZK:$((L_PRED-1))" )

# 11: Predictive + Comparison
FILES+=( "11-predictive-and-comparison.md" )
TITLES+=( "Predictive Holonomy + Comparison" )
RANGES+=( "$L_PRED:$((L_CONC-1))" )

# 12: Conclusion + Acknowledgments + Appendix (to end)
FILES+=( "12-conclusion-ack-appendix.md" )
TITLES+=( "Conclusion + Acknowledgments + Appendix" )
RANGES+=( "$L_CONC:$L_END" )

# emit & commit
COUNT="${#FILES[@]}"
for i in $(seq 0 $((COUNT-1))); do
  f="${FILES[$i]}"; t="${TITLES[$i]}"; r="${RANGES[$i]}"
  a="${r%%:*}"; b="${r##*:}"
  out="$TARGET_DIR/$f"
  slice "$a" "$b" "$out"
  git add "$out" >/dev/null 2>&1 || true
  git commit -q -m "monographs: add $f — $t [lines $a..$b]" || true
  echo "[ok] $f  <-  lines $a..$b"
done

# write an ORDER file for rebuilds
ORDER="$TARGET_DIR/ORDER.txt"
printf "%s\n" "${FILES[@]}" > "$ORDER"
git add "$ORDER" >/dev/null 2>&1 || true
git commit -q -m "monographs: add ORDER.txt for dlr-bordisms" || true

echo "[done] split into $COUNT chunks in $TARGET_DIR"
