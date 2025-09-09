#!/usr/bin/env bash
set -euo pipefail
mkdir -p .tau_ledger
# pick a statement file (prefer lake-manifest.json, else manifests/*.json, else synthesize)
STMT="$(git ls-files lake-manifest.json 'manifests/*.json' | head -n1 || true)"
if [ -z "${STMT:-}" ]; then printf '{ "note":"synthetic statement (none present)" }\n' > .tau_ledger/statement.json; STMT=".tau_ledger/statement.json"; fi

read -r S_DIG S_ALGO < <("$(dirname "$0")/hash.sh" "$STMT")
read -r G_DIG G_ALGO < <("$(dirname "$0")/grammar_hash.sh")
TS="$(date -u +%Y-%m-%dT%H:%M:%SZ)"; COMMIT="$(git rev-parse HEAD 2>/dev/null || echo unknown)"
REPO="${GITHUB_SERVER_URL:-https://github.com}/${GITHUB_REPOSITORY:-unknown}"
# write receipt deterministically (no heredoc pitfalls)
{
  printf '{'
  printf '"version":"rcpt-3",'
  printf '"timestamp":"%s",' "$TS"
  printf '"repo":"%s",' "$REPO"
  printf '"commit":"%s",' "$COMMIT"
  printf '"grammar_digest":"%s","grammar_algo":"%s",' "$G_DIG" "$G_ALGO"
  printf '"statement_digest":"%s","statement_algo":"%s",' "$S_DIG" "$S_ALGO"
  printf '"status":"synthetic"'
  printf '}\n'
} > .tau_ledger/receipt.json
read -r R_DIG R_ALGO < <("$(dirname "$0")/hash.sh" .tau_ledger/receipt.json)

# print key=value once; caller captures and fans out to $GITHUB_OUTPUT and summary
printf "receipt_path=.tau_ledger/receipt.json\n"
printf "receipt_digest=%s\n"        "$R_DIG"
printf "receipt_algo=%s\n"          "$R_ALGO"
printf "statement=%s\n"             "$STMT"
printf "statement_digest=%s\n"      "$S_DIG"
printf "statement_algo=%s\n"        "$S_ALGO"
printf "grammar_file=%s\n"          "${GRAMMAR_FILE:-verify/ReceiptGrammar.lean}"
printf "grammar_digest=%s\n"        "$G_DIG"
printf "grammar_algo=%s\n"          "$G_ALGO"
# also echo JSON for convenience
printf -- "---\n%s\n" "$(cat .tau_ledger/receipt.json)"
