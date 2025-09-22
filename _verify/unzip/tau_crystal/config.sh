#!/usr/bin/env bash
ROOT="$(realpath "$HOME/Desktop/tau_crystal/tau_crystal")"
LEDGER=".tau_ledger"
MANIFEST="docs/manifest.md"
[ -d "$ROOT" ] || { echo "[err] invalid ROOT: $ROOT"; exit 10; }
