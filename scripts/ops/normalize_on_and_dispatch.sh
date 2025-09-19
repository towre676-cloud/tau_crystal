#!/usr/bin/env bash
set -Ee -o pipefail; set +H; umask 022
shopt -s nullglob
for y in .github/workflows/*.yml .github/workflows/*.yaml; do
  [ -f "$y" ] || continue
  if grep -qE "^[[:space:]]*workflow_dispatch[[:space:]]*:" "$y"; then printf "keep   %s (already dispatchable)\n" "$y"; continue; fi
  if grep -qE "^[[:space:]]*on:[[:space:]]*\\[[^\\]]*\\][[:space:]]*$" "$y"; then
    tmp="$(mktemp -t wf.XXXX)"; trap 'rm -f "$tmp"' EXIT
    awk '
/^[[:space:]]*on:[[:space:]]*\\[/ { 
  pre=gensub(/^( *).*/, "\\\\1", 1, $0); 
  g=$0; 
  g=gensub(/^[[:space:]]*on:[[:space:]]*\\[([^\\]]*)\\][[:space:]]*$/, "\\\\1", 1, g); 
  n=split(g, a, /[[:space:]]*,[[:space:]]*/); 
  print pre "on:"; 
  for (i=1;i<=n;i++) { e=a[i]; gsub(/^[[:space:]]+|[[:space:]]+$/, "", e); if (e!="") print pre "  " e ":"; } 
  print pre "  workflow_dispatch:"; next } 
{ print }
  fi
  if grep -qE "^[[:space:]]*on:[[:space:]]*\\{[^\\}]*\\}[[:space:]]*$" "$y"; then
    tmp="$(mktemp -t wf.XXXX)"; trap 'rm -f "$tmp"' EXIT
    awk '
/^[[:space:]]*on:[[:space:]]*\\{/ { 
  pre=gensub(/^( *).*/, "\\\\1", 1, $0); 
  g=$0; g=gensub(/^[[:space:]]*on:[[:space:]]*\\{([^}]*)\\}[[:space:]]*$/, "\\\\1", 1, g); 
  n=split(g, a, /[[:space:]]*,[[:space:]]*/); 
  print pre "on:"; 
  for (i=1;i<=n;i++) { kv=a[i]; split(kv, p, /:/); e=p[1]; gsub(/^[[:space:]]+|[[:space:]]+$/, "", e); if (e!="") print pre "  " e ":"; } 
  print pre "  workflow_dispatch:"; next } 
{ print }
  fi
  if grep -qE "^[[:space:]]*on:[[:space:]]*$" "$y"; then
    tmp="$(mktemp -t wf.XXXX)"; trap 'rm -f "$tmp"' EXIT
    awk '
/^[[:space:]]*on:[[:space:]]*$/ { print; print "  workflow_dispatch:"; next } { print }
  fi
  printf "skip   %s (complex on: — manual)\n" "$y"
done
