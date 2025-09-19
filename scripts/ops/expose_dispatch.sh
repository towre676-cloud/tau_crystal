#!/usr/bin/env bash
set -Ee -o pipefail; set +H; umask 022
shopt -s nullglob
patched=0
for y in .github/workflows/*.yml .github/workflows/*.yaml; do
  [ -f "$y" ] || continue
  grep -qE "^[[:space:]]*workflow_dispatch[[:space:]]*:" "$y" && { echo "keep  $y"; continue; }
  if grep -qE "^[[:space:]]*on:[[:space:]]*\\[[^]]*\\][[:space:]]*$" "$y"; then
    grep -q "workflow_dispatch" "$y" || { sed -i -E "s/^([[:space:]]*on:[[:space:]]*\\[[^]]*)\\]/\\1, workflow_dispatch]/" "$y"; echo "patch $y (inline list)"; patched=1; }
    continue
  fi
  if grep -qE "^[[:space:]]*on:[[:space:]]*\\{[^}]*\\}[[:space:]]*$" "$y"; then
    grep -q "workflow_dispatch" "$y" || { sed -i -E "s/^([[:space:]]*on:[[:space:]]*\\{[^}]*)\\}/\\1, workflow_dispatch: {}}/" "$y"; echo "patch $y (inline map)"; patched=1; }
    continue
  fi
  if grep -qE "^[[:space:]]*on:[[:space:]]*$" "$y"; then
