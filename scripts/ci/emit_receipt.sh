#!/usr/bin/env bash
set -Eeuo pipefail; set +H
. scripts/rc/common.sh
TAU_CLASS="${TAU_CLASS:-work}"; case "$TAU_CLASS" in ensemble|work) : ;; *) TAU_CLASS=work ;; esac
mkdir -p receipts signals
WORK=signals/work.raw; MEM=signals/mem.raw
[ -f "$WORK" ] || { echo "missing signals/work.raw" >&2; exit 3; }
BEST=$(scripts/ci/param_sweep.sh "$WORK"); eval "$BEST"  # sets K, OMEGA
TMP="$(mktemp -d)"; trap "rm -rf \"$TMP\"" EXIT
awk -v K="$K" -v W="$OMEGA" -f scripts/ci/smooth.awk "$WORK" > "$TMP/work.tau"
FUSE=0; if [ "$TAU_CLASS" = "ensemble" ] && [ -f "$MEM" ]; then FUSE=1; fi
if [ "$FUSE" = "1" ]; then
  awk -f scripts/ci/norm01_rank.awk "$MEM" > "$TMP/mem.norm"
  paste -d" " "$TMP/work.tau" "$TMP/mem.norm" | awk -f scripts/ci/avg2.awk | awk -f scripts/ci/pav.awk > "$TMP/tau.final"
else
  cp "$TMP/work.tau" "$TMP/tau.final"
fi
WR=$(tr -d " \r" < "$WORK" | tr "\n" "," | sed -e "s/,$//")
WT=$(tr -d " \r" < "$TMP/work.tau" | tr "\n" "," | sed -e "s/,$//")
TAU=$(tr -d " \r" < "$TMP/tau.final" | tr "\n" "," | sed -e "s/,$//")
MR=""; if [ "$FUSE" = "1" ]; then MR=$(tr -d " \r" < "$MEM" | tr "\n" "," | sed -e "s/,$//"); fi
STAMP="$(iso_now)"; SHA="$(git_sha)"; HOST="$(hostname_s)"; BVER="${BASH_VERSION:-unknown}"
OUT="receipts/${STAMP//:/-}.json"; : > "$OUT"
echo "{" >> "$OUT"
echo "  \"schema\":\"taucrystal/receipt/v1\"," >> "$OUT"
echo "  \"tau_class\":\"$TAU_CLASS\"," >> "$OUT"
printf "  \"params\":{\"K\":%s,\"omega\":%.2f},\n" "$K" "$OMEGA" >> "$OUT"
printf "  \"provenance\":{\"git_commit\":\"%s\",\"timestamp\":\"%s\",\"host\":\"%s\",\"bash\":\"%s\"},\n" "$SHA" "$STAMP" "$HOST" "$BVER" >> "$OUT"
printf "  \"signals\":{\"work_raw\":[%s],\"work_tau\":[%s]" "$WR" "$WT" >> "$OUT"
if [ "$FUSE" = "1" ]; then printf ",\"mem_raw\":[%s]" "$MR" >> "$OUT"; fi
echo "  }," >> "$OUT"
printf "  \"tau\":[%s]\n" "$TAU" >> "$OUT"
echo "}" >> "$OUT"
echo "$OUT"
