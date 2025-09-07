#!/usr/bin/env bash
set -euo pipefail

repo="$(git rev-parse --show-toplevel 2>/dev/null || pwd)"
cd "$repo"

out_dir=".tau_ledger"
mkdir -p "$out_dir"

stamp="$(date -u +%Y%m%dT%H%M%SZ)"
commit="$(git rev-parse --short=12 HEAD 2>/dev/null || echo 'WORKTREE')"
ndjson="$out_dir/assumptions-$stamp.ndjson"
tsv="$out_dir/assumptions-$stamp.tsv"

# reset outputs
: > "$ndjson"
: > "$tsv"

# helper: trim line comment tail
strip_tail() { sed 's/[[:space:]]--.*$//' ; }

# scan all lean sources in git
git ls-files -z -- '*.lean' | while IFS= read -r -d '' f; do
  ln=0
  while IFS= read -r line || [ -n "$line" ]; do
    ln=$((ln+1))
    clean="$(printf '%s\n' "$line" | strip_tail)"
    case "$clean" in
      (""|*[![:space:]]*)
        # axiom <Name>
        if printf '%s\n' "$clean" | grep -qE '^[[:space:]]*axiom[[:space:]]+'; then
          name="$(printf '%s\n' "$clean" | sed -E 's/^[[:space:]]*axiom[[:space:]]+([A-Za-z0-9_.'\''-]+).*/\1/')"
          kind="axiom"
        # opaque <Name>
        elif printf '%s\n' "$clean" | grep -qE '^[[:space:]]*opaque[[:space:]]+'; then
          name="$(printf '%s\n' "$clean" | sed -E 's/^[[:space:]]*opaque[[:space:]]+([A-Za-z0-9_.'\''-]+).*/\1/')"
          kind="opaque"
        # unsafe def/theorem/abbrev/opaque/inductive/structure <Name>
        elif printf '%s\n' "$clean" | grep -qE '^[[:space:]]*unsafe[[:space:]]+(def|theorem|abbrev|opaque|inductive|structure)[[:space:]]+'; then
          name="$(printf '%s\n' "$clean" | sed -E 's/^[[:space:]]*unsafe[[:space:]]+(def|theorem|abbrev|opaque|inductive|structure)[[:space:]]+([A-Za-z0-9_.'\''-]+).*/\2/')"
          kind="unsafe"
        else
          continue
        fi

        # emit (skip empty names just in case)
        if [ -n "${name:-}" ]; then
          printf '{"kind":"%s","name":"%s","file":"%s","line":%d,"commit":"%s"}\n' \
            "$kind" "$name" "$f" "$ln" "$commit" >> "$ndjson"
          printf '%s\t%s\t%s\t%d\n' "$kind" "$name" "$f" "$ln" >> "$tsv"
        fi
      ;;
    esac
  done < "$f"
done

# stable symlinks for consumers
cp "$ndjson" "$out_dir/assumptions.ndjson"
cp "$tsv"    "$out_dir/assumptions.tsv"

echo "$ndjson"
