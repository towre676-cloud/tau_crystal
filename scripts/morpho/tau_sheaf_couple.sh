#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
# Usage: tau_sheaf_couple.sh <receipt.json> subject=<id> metric=<name> value=<num> [tag=...] [note=...]
REC="${1:-}"; shift || true
[ -n "$REC" ] && [ -s "$REC" ] || { echo "[tau_couple] missing receipt"; exit 2; }
SUBJ="anon"; NAME="metric"; VAL="NaN"; TAG=""; NOTE=""
for kv in "$@"; do
  case "$kv" in
    subject=*) SUBJ="${kv#subject=}" ;;
    metric=*)  NAME="${kv#metric=}" ;;
    value=*)   VAL="${kv#value=}" ;;
    tag=*)     TAG="${kv#tag=}" ;;
    note=*)    NOTE="${kv#note=}" ;;
  esac
done
RHS="$(sha256sum "$REC" 2>/dev/null | awk "{print \$1}")"
[ -n "$RHS" ] || { echo "[tau_couple] sha256sum unavailable"; exit 3; }
TS="$(date -u +"%Y-%m-%dT%H:%M:%SZ")"
EV=".tau_ledger/tau_sheaf/events.jsonl"; TSV="analysis/morpho/tau_coupling.tsv"
PRV=""; [ -s "$EV" ] && PRV="$(tail -n 1 "$EV" | sha256sum | awk "{print \$1}")"
LID="$(printf "%s" "$TS-$SUBJ-$RHS-$NAME-$VAL" | sha256sum | awk "{print \$1}")"
mkdir -p "$(dirname "$EV")" "$(dirname "$TSV")"
J="{\"kind\":\"tau_sheaf/morpho\",\"timestamp\":\"'$TS'\",\"subject\":\"'$SUBJ'\",\"metric\":\"'$NAME'\",\"value\":'$VAL',\"receipt_sha256\":\"'$RHS'\",\"prev\":\"'$PRV'\",\"lid\":\"'$LID'\""
if [ -n "$TAG" ]; then J="$J,\"tag\":\"'$TAG'\""; fi
if [ -n "$NOTE" ]; then J="$J,\"note\":\"'$NOTE'\""; fi
J="$J}"; printf "%s\n" "$J" >> "$EV"
if [ ! -s "$TSV" ]; then printf "%s\n" "timestamp\tsubject\tmetric\tvalue\treceipt_sha256\tprev\tlid\ttag\tnote" > "$TSV"; fi
printf "%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n" "$TS" "$SUBJ" "$NAME" "$VAL" "$RHS" "$PRV" "$LID" "$TAG" "$NOTE" >> "$TSV"
echo "[tau_couple] appended event (lid=$LID) and updated $TSV"
