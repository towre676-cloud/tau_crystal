#!/usr/bin/env bash
. "$(dirname "$0")/../safe/_env.sh"
set -e
cd "$HOME/Desktop/tau_crystal/tau_crystal" || exit 1
./scripts/meta/k3_next_verify.sh
