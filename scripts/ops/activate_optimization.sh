#!/usr/bin/env bash
cd "$HOME/Desktop/tau_crystal/tau_crystal" || exit 1
set -E -o pipefail; set +H; umask 022
printf "[opt] Activating placeholder for optimization ID: %s\n" "${1:-none}"
