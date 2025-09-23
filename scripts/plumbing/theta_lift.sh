#!/usr/bin/env bash
set +H
. scripts/plumbing/_lib.sh || exit 1
SRC="${1:?src box}"; DST="${2:?dst box}"; WEIGHT="${3:-1}"
safe_mkdir ".tau_ledger/hysteresis/$SRC"
out=".tau_ledger/hysteresis/${SRC}/theta_to_${DST}.json"
write_json "$out" "src" "$SRC" "dst" "$DST" "weight" "$WEIGHT" "kernel" "theta" "at" "$(date -u +%Y-%m-%dT%H:%M:%SZ)"
log "theta_lift: $SRC -> $DST w=$WEIGHT -> $out"
