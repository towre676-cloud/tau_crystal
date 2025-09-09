#!/usr/bin/env bash
set -euo pipefail
set +H

resolve_ref(){
  local repo_root="$1" ref="$2" url="https://github.com/${repo_root}.git" sha=""
  sha="$(git ls-remote --tags  "$url" "refs/tags/$ref^{}" 2>/dev/null | awk "NR==1{print \$1}")"
  [ -n "$sha" ] || sha="$(git ls-remote --tags  "$url" "refs/tags/$ref"    2>/dev/null | awk "NR==1{print \$1}")"
  [ -n "$sha" ] || sha="$(git ls-remote --heads "$url" "$ref"              2>/dev/null | awk "NR==1{print \$1}")"
  [ -n "$sha" ] || sha="$(git ls-remote         "$url" "$ref"              2>/dev/null | awk "NR==1{print \$1}")"
  printf "%s" "$sha"
}

pin_file(){
  local f="$1" changed=0
  sed -i 's/\r$//' "$f" 2>/dev/null || true
  while IFS= read -r L; do
    spec=$(printf "%s" "$L" | sed -E 's/.*uses:[[:space:]]*([^@[:space:]]+)@([^[:space:]]+).*/\1/')
    ref=$( printf "%s" "$L" | sed -E 's/.*uses:[[:space:]]*([^@[:space:]]+)@([^[:space:]]+).*/\2/')
    [ -n "$spec" ] && [ -n "$ref" ] || continue
    case "$spec" in ./*|*/.*) continue;; esac  # skip local actions
    printf "%s" "$ref" | grep -qE '^[0-9a-f]{40}$' && continue
    owner="${spec%%/*}"; rest="${spec#*/}"; repo="${rest%%/*}"
    if [ "$owner/$repo" = "$spec" ]; then subpath=""; else subpath="${rest#*/}"; fi
    repo_root="$owner/$repo"
    sha="$(resolve_ref "$repo_root" "$ref")"
    if [ -n "$sha" ]; then
      # build new uses: with pinned sha
      new="uses: ${repo_root}${subpath:+/}${subpath:+$subpath}@$sha"
      # escape the OLD (search) and NEW (replacement) strings for sed with | delimiter
      old="${spec}@${ref}"
      esc_old=$(printf "%s" "$old" | sed -E 's/[|\\&]/\\&/g')
      esc_new=$(printf "%s" "$new" | sed -E 's/[|\\&]/\\&/g')
      sed -i -E "0,/uses:[[:space:]]*${esc_old}/s|uses:[[:space:]]*${esc_old}|${esc_new}|" "$f"
      echo "[pin] $f: ${spec}@${ref} -> ${sha}"
      changed=1
    else
      echo "[warn] could not resolve ${spec}@${ref}"
    fi
  done < <(grep -nE 'uses:[[:space:]]*[^@[:space:]]+@[^[:space:]]+' "$f" | grep -vE '@([0-9a-f]{40})([[:space:]]*(#.*)?)?$')
  return "$changed"
}

any=0
for WF in .github/workflows/*.yml .github/workflows/*.yaml; do
  [ -f "$WF" ] || continue
  pin_file "$WF" && any=1 || true
done
[ "$any" -eq 1 ] && echo "[ok] pinning pass complete" || echo "[ok] nothing to pin (or already pinned)"
