#!/usr/bin/env bash
set +H
set -euo pipefail
IFS=$(printf '\n\t')

REPO_ROOT="$PWD"
[ -d ".git" ] || { printf "Not a git repo: %s\n" "$REPO_ROOT" >&2; exit 1; }

REG_DIR="$REPO_ROOT/.tau_ledger/registry"
mkdir -p "$REG_DIR"

timestamp_utc="$(date -u +%Y%m%dT%H%M%SZ)"
OUT="$REG_DIR/history_${timestamp_utc}.tsv"
LATEST="$REPO_ROOT/.tau_ledger/REGISTRY_HISTORY.tsv"

printf 'ts\ttype\tsha256\tmerkle_root\tsize_bytes\tsource\tpath\tgit_commit\tgit_status\n' > "$OUT"

hash_file() {
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum "$1" | awk '{print $1}'
  elif command -v shasum >/dev/null 2>&1; then
    shasum -a 256 "$1" | awk '{print $1}'
  else
    openssl dgst -sha256 -r "$1" | awk '{print $1}'
  fi
}

pattern="merkle[_-]*(root|hash|digest)|manifest[_-]*(sha256|digest|root)|receipt|ledger"

git log --all -G"$pattern" --pretty=format:%H --name-only -- '*.json' |
awk "BEGIN{c=\"\"} /^[0-9a-f]{40}\$/{c=\$0; next} NF && c!=\"\" {print c \"\t\" \$0}" |
sort -u |
while IFS=$'\t' read -r commit path; do
  if ! git cat-file -e "${commit}:${path}" 2>/dev/null; then
    continue
  fi
  tmp="$(mktemp)"
  git show "${commit}:${path}" > "$tmp" 2>/dev/null || { rm -f "$tmp"; continue; }
  if ! grep -I -i -E -m1 "$pattern" "$tmp" >/dev/null 2>&1; then
    rm -f "$tmp"; continue
  fi
  merkle="$(awk "BEGIN{IGNORECASE=1} match(\$0,/\"merkle[_-]*root\"[[:space:]]*:[[:space:]]*\"([^\"]+)\"/,a){print a[1]; exit}" "$tmp" 2>/dev/null || true)"
  sha="$(hash_file "$tmp")"
  blob="$(git ls-tree "$commit" -- "$path" | awk '{print $3}' | head -n1)"
  size_bytes=""
  if [ -n "$blob" ]; then
    size_bytes="$(git cat-file -s "$blob" 2>/dev/null || printf "")"
  fi
  ts_row="$(git show -s --format=%cI "$commit" 2>/dev/null || date -u +%Y-%m-%dT%H:%M:%SZ)"
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
    "$ts_row" "receipt" "$sha" "$merkle" "$size_bytes" "git" "$path" "$commit" "committed" >> "$OUT"
  rm -f "$tmp"
done

cp -f "$OUT" "$LATEST"
printf "Wrote %s\n" "$OUT"
printf "Updated latest history -> %s\n" "$LATEST"
