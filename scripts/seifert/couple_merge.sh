cd "$HOME/Desktop/tau_crystal/tau_crystal" || exit 1
set -euo pipefail; set +H; umask 022
REC="${1:?receipt json}"
AI_RAW="${2:-}"
E_VAL="${3:-0}"
KIN="${4:-1.0}"
TMP=".cache/couple_merge.$$__py.py"; : > "$TMP"
cat .cache/couple_merge.stub > "$TMP"
PYTHONPATH=".:$PYTHONPATH" python "$TMP" "$REC" "$AI_RAW" "$E_VAL" "$KIN" | tr -d "\r" || true
rm -f "$TMP" 2>/dev/null || true
