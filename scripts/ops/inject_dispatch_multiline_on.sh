#!/usr/bin/env bash
set -Ee -o pipefail; set +H; umask 022
shopt -s nullglob
for y in .github/workflows/*.yml .github/workflows/*.yaml; do
  [ -f "$y" ] || continue
  # Skip if already has workflow_dispatch
  grep -qE "^[[:space:]]*workflow_dispatch[[:space:]]*:" "$y" && { printf "keep   %s (already dispatchable)\n" "$y"; continue; }
  # Skip inline on: […] or on: {…}
  grep -qE "^[[:space:]]*on:[[:space:]]*[\{\[]+" "$y" && { printf "skip   %s (inline on: — manual)\n" "$y"; continue; }
  # Handle multi-line on: blocks
  if grep -qE "^[[:space:]]*on:[[:space:]]*$" "$y"; then
    t="$(mktemp -t wfdisp.XXXXXX)"; trap 'rm -f "$t"' EXIT
    inserted=0
    while IFS= read -r line || [ -n "$line" ]; do
      printf "%s\n" "$line" >> "$t"
      if [ $inserted -eq 0 ] && printf "%s" "$line" | grep -qE "^[[:space:]]*on:[[:space:]]*$"; then
        IFS= read -r next || true
        indent="$(printf "%s" "$next" | sed -E "s/^([[:space:]]*).*/\1/")"
        printf "%s%s\n" "$indent" "workflow_dispatch:" >> "$t"
        printf "%s\n" "$next" >> "$t"
        inserted=1
      fi
    done < "$y"
    mv "$t" "$y"
    printf "patch  %s (+ workflow_dispatch)\n" "$y"
  else
    printf "skip   %s (no bare multi-line on: — manual)\n" "$y"
  fi
done
