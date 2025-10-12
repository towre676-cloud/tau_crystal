#!/usr/bin/env bash
set +H
set -euo pipefail
IFS=$(printf '\n\t')

REPO_ROOT="$PWD"
[ -d ".git" ] || { printf "Not a git repo: %s\n" "$REPO_ROOT" >&2; exit 1; }
REG_DIR="$REPO_ROOT/.tau_ledger/registry"
mkdir -p "$REG_DIR"
timestamp_utc="$(date -u +%Y%m%dT%H%M%SZ)"
