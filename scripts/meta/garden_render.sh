#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022

ROOT="$(git rev-parse --show-toplevel 2>/dev/null || pwd)"
cd "$ROOT" || exit 1

# ensure worktree
if ! git show-ref --verify --quiet refs/heads/garden; then git branch garden 2>/dev/null || git checkout -b garden; fi
[ -d .garden/.git ] || git worktree add -f .garden garden

IDX=".garden/index.jsonl"
[ -s "$IDX" ] || { echo "[garden:render] missing $IDX"; exit 0; }

OUT=".garden/index.html"
TMP="$OUT.tmp.$$"

# simple HTML header
{
  echo '<!doctype html><meta charset="utf-8"><title>τ-Crystal Automorphic Garden</title>'
  echo '<style>body{font:14px system-ui,Segoe UI,Roboto,Arial,sans-serif;background:#0b0d11;color:#e6e7ea;margin:2rem} a{color:#8fbaff;text-decoration:none}'
  echo 'table{border-collapse:collapse;width:100%} th,td{padding:.4rem .6rem;border-bottom:1px solid #222} tr:hover{background:#12151c}'
  echo 'code{background:#12151c;padding:.1rem .3rem;border-radius:.3rem}</style>'
  echo '<h1>τ-Crystal Automorphic Garden</h1>'
  echo '<p>Latest contributions from receipts and Δ-surfaces. Each row links to its shard with plots and artifacts.</p>'
  echo '<table><thead><tr><th>UTC</th><th>Host</th><th>Branch@Head</th><th>Rows</th><th>Minima</th><th>Best Δ</th><th>Shard</th><th>Plots</th></tr></thead><tbody>'
} > "$TMP"

# read last 50 entries (tail) and render
tail -n 50 "$IDX" | while IFS= read -r line; do
  # pull fields without jq
  utc="$(printf '%s' "$line" | sed -n 's/.*"utc":"\([^"]*\)".*/\1/p')"
  host="$(printf '%s' "$line" | sed -n 's/.*"host":"\([^"]*\)".*/\1/p')"
  branch="$(printf '%s' "$line" | sed -n 's/.*"branch":"\([^"]*\)".*/\1/p')"
  head="$(printf '%s' "$line" | sed -n 's/.*"head":"\([^"]*\)".*/\1/p')"
  rows="$(printf  '%s' "$line" | sed -n 's/.*"scan_rows":\([^,}]*\).*/\1/p')"
  mins="$(printf  '%s' "$line" | sed -n 's/.*"minima":\([^,}]*\).*/\1/p')"
  bestD="$(printf '%s' "$line" | sed -n 's/.*"best":{"delta":\([^,}]*\).*/\1/p')"

  # day shard from UTC, e.g., 2025-09-15T17:00:00Z -> 2025/09/15
  day="$(printf '%s' "$utc" | sed -n 's/^\([0-9]\{4\}\)-\([0-9]\{2\}\)-\([0-9]\{2\}\).*/\1\/\2\/\3/p')"
  shard="contrib/${day}/${host}/${head}"

  # detect plots present
  PLOT_LINKS=""
  for p in "analysis/plots/atlas_line.svg" "analysis/plots/basins.svg" "analysis/plots/morse.svg" "analysis/plots/satake_polar.svg"; do
    if [ -f ".garden/${shard}/$(basename "$p")" ]; then
      name="$(basename "$p")"
      PLOT_LINKS="$PLOT_LINKS <a href=\"${shard}/${name}\">${name}</a>"
    elif [ -f ".garden/${shard}/${p}" ]; then
      PLOT_LINKS="$PLOT_LINKS <a href=\"${shard}/${p}\">$(basename "$p")</a>"
    fi
  done
  [ -z "$PLOT_LINKS" ] && PLOT_LINKS='—'

  printf '<tr><td>%s</td><td>%s</td><td><code>%s@%s</code></td><td>%s</td><td>%s</td><td>%s</td><td><a href="%s">shard</a></td><td>%s</td></tr>\n' \
    "$utc" "$host" "$branch" "$head" "${rows:-0}" "${mins:-0}" "${bestD:-—}" "$shard" "$PLOT_LINKS" >> "$TMP"
done

echo '</tbody></table><p>Branch: <code>garden</code>. File: <code>.garden/index.jsonl</code>.</p>' >> "$TMP"
mv "$TMP" "$OUT"

git -C .garden add index.html
git -C .garden commit -m "garden: render index.html" 2>/dev/null || true
git -C .garden push -u origin garden
echo "[garden:render] updated .garden/index.html"
