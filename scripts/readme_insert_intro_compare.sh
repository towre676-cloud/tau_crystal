#!/usr/bin/env bash
set -euo pipefail
ROOT="$HOME/Desktop/tau_crystal/tau_crystal"; cd "$ROOT" || { echo "[err] bad root"; exit 1; }
README="README.md"; [ -f "$README" ] || : > "$README"
INTRO="$(mktemp)"; COMP="$(mktemp)"
printf "%s\n" "## τ-Crystal — proof-carrying runtime manifest for reproducible compute" >>"$INTRO"
printf "\n%s\n" "τ-Crystal turns a repository into a self-verifying project. Every run emits a receipt chained by SHA-256, stamps a repository-wide MERKLE_ROOT over tracked files, and writes a live STATUS line to docs/manifest.md. The result is a one-line, machine-checkable claim you can quote in issues, papers, and audits." >>"$INTRO"
printf "\n%s\n" "**Why it matters:** traditional pipelines hash outputs or bundle environments, but they don’t prove the execution path. τ-Crystal makes divergence explicit and small: the CHAIN head changes if and only if the verified path changed." >>"$INTRO"
printf "\n%s\n" "**What you get today (bash-only):**" >>"$INTRO"
printf "%s\n" "– Execution-state receipts + CHAIN" >>"$INTRO"
printf "%s\n" "– Repository MERKLE_ROOT + manifest STATUS" >>"$INTRO"
printf "%s\n" "– Same flow locally and in CI (no containers required)" >>"$INTRO"
printf "%s\n" "– Free tier to prove value; Pro adds required proof gates, higher throughput, and longer retention" >>"$INTRO"
printf "\n%s\n" "**Prove it fast:** run the pinned “Verify this release (v0.1.0)” snippet below, then try the Golden diff demo (perturb one tracked file and watch the head change). Keep your science/dev runnable—and provable—without heavy tooling. When you need org-wide enforcement, turn on Pro." >>"$INTRO"
printf "%s\n" "## Why this is different" >>"$COMP"
printf "%s\n" "**Compared to common tools**" >>"$COMP"
printf "%s\n" "– Git: versions sources, but no runtime receipts/CHAIN" >>"$COMP"
printf "%s\n" "– Containers: portable environments, opaque execution paths" >>"$COMP"
printf "%s\n" "– Notebooks: interactive, non-deterministic order" >>"$COMP"
printf "%s\n" "– τ-Crystal: execution-state receipts + CHAIN head + MERKLE_ROOT + manifest STATUS" >>"$COMP"
printf "%s\n" "– Works in CI with bash-only drops; enforce with Pro when required" >>"$COMP"
printf "%s\n" "– One-line head diff shows exactly when the path diverged" >>"$COMP"
if ! grep -q "^## τ-Crystal — proof-carrying runtime manifest for reproducible compute" "$README"; then
  TMP="$(mktemp)";
  awk -v intro="$INTRO" 'BEGIN{ins=0} {print} /^## Quickstart$/ && !ins {print ""; while ((getline l < intro)>0) print l; close(intro); print ""; ins=1}' "$README" >"$TMP" && mv "$TMP" "$README"
fi
grep -q "^## Why this is different" "$README" || { printf "\n" >>"$README"; cat "$COMP" >>"$README"; }
rm -f "$INTRO" "$COMP"
echo "[readme] intro+comparison inserted (idempotent)."
