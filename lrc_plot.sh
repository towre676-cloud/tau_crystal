#!/usr/bin/env sh
# Usage: ./lrc_plot.sh summary.csv
CSV="${1:-lrc_summary.csv}"
if ! command -v gnuplot >/dev/null 2>&1; then
  echo "gnuplot not found; skipping plots." >&2
  exit 0
fi

cat > _plot_hit_rate.gp <<'GP'
set term pngcairo size 900,500
set output "hit_rate_vs_k.png"
set datafile separator ","
set grid
set xlabel "k"
set ylabel "hit-rate (exact 1/(k+1))"
plot "lrc_summary.csv" using 1:5 with linespoints title "hit-rate"
GP

cat > _plot_mean_slack.gp <<'GP'
set term pngcairo size 900,500
set output "mean_slack_vs_k.png"
set datafile separator ","
set grid
set xlabel "k"
set ylabel "mean slack (discrete max - 1/(k+1))"
plot "lrc_summary.csv" using 1:6 with linespoints title "mean slack"
GP

cp "$CSV" lrc_summary.csv
gnuplot _plot_hit_rate.gp
gnuplot _plot_mean_slack.gp
rm -f _plot_hit_rate.gp _plot_mean_slack.gp
echo "Wrote: hit_rate_vs_k.png, mean_slack_vs_k.png"
