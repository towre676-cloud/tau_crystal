#!/usr/bin/env bash
set -euo pipefail; set +H
R="analysis/obstructions/tpc_report.tsv"; [ -s "$R" ] || exit 0
dest="${GITHUB_STEP_SUMMARY:-}"; [ -n "$dest" ] || exit 0
{
  echo "### Čech \(H^1\) Obstruction Check (3-patch)";
  echo ""; echo "| cover | kernel | triple | class |"; echo "|---|---|---|---|";
  awk -F"\t" 'NR>1{printf("| %s | %s | %s | %s |\n",$1,$2,$6,$7)}' "$R"
} >> "$dest"
