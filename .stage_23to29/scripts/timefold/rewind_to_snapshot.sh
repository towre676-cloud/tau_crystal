cd "$HOME/Desktop/tau_crystal/tau_crystal" || exit 1
set -euo pipefail; umask 022; export LC_ALL=C LANG=C
snap="${1:-}"; label="${2:-}"
if [ -z "$snap" ]; then snap=$(ls -1 .tau_ledger/timefold/*_snapshot.json 2>/dev/null | tail -n 1 || true); fi
[ -s "$snap" ] || { echo "[err] no snapshot receipt found"; exit 2; }
val(){ sed -n "s/.*\"$1\":\"\\([^\"]*\\)\".*/\\1/p" "$snap" | head -n1; }
snap_ts=$(val ts); snap_sha=$(val git_sha); snap_tree=$(val tree_sha256)
cur_sha="$(git rev-parse --verify HEAD 2>/dev/null || printf "%s" none)"
ts="$(date -u +%FT%TZ)"
DF=".tmp.timefold_diff.$$"; : > "$DF"; (git diff --name-status "$snap_sha" "$cur_sha" || true) > "$DF"
diff_lines=$(wc -l < "$DF" | tr -d "[:space:]")
diff_sha=$(openssl dgst -sha256 "$DF" | awk "{print \$2}")
rm -f "$DF"
out=".tau_ledger/timefold/${ts//:/-}_rewind_plan.json"; : > "$out"
printf "%s" "{" >> "$out"
printf "%s" "\"ts\":\"$ts\",\"intent\":\"rewind\",\"label\":\"$(printf "%s" "$label" | sed 's/\"/\047/g')\"," >> "$out"
printf "%s" "\"from\":{\"git_sha\":\"$cur_sha\"},\"to\":{\"git_sha\":\"$snap_sha\",\"snapshot_ts\":\"$snap_ts\",\"tree_sha256\":\"$snap_tree\"}," >> "$out"
printf "%s" "\"diff_digest\":{\"sha256\":\"$diff_sha\",\"lines\":$diff_lines}}" >> "$out"
echo "[ok] rewind plan → $out (no mutation performed)"
