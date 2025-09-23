#!/usr/bin/env bash
set -Ee -o pipefail; set +H; umask 022
shopt -s nullglob
changed=0
for y in .github/workflows/*.yml .github/workflows/*.yaml; do
  [ -f "$y" ] || continue
  if grep -qE "^[[:space:]]*workflow_dispatch[[:space:]]*:" "$y"; then
    printf "keep   %s (already dispatchable)\n" "$y"
    continue
  fi
  if grep -qE "^[[:space:]]*on:[[:space:]]*$" "$y"; then
    t="$(mktemp -t wfdisp.XXXXXX)"; trap 'rm -f "$t"' EXIT
    awk '/^[[:space:]]*on:[[:space:]]*$/ { print; print "  workflow_dispatch:"; next } { print }' "$y" > "$t"
    mv "$t" "$y"
    printf "patch  %s (+ workflow_dispatch)\n" "$y"
    changed=1
  else
    printf "skip   %s (inline or complex on: — edit manually)\n" "$y"
  fi
done
exit 0
