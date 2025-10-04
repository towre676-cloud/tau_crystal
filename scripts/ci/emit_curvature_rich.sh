#!/usr/bin/env bash
# rich curvature emitter (deterministic LCG; zero-sum; MSYS-safe)
umask 022; export LC_ALL=C LANG=C
LEDGER_DIR=${LEDGER_DIR:-.tau_ledger}
N=${N:-3}
mkdir -p "$LEDGER_DIR" 2>/dev/null || :
i=1
while [ "$i" -le "$N" ]; do
  f="$LEDGER_DIR/rich_r${i}_curvature.tsv"
  : > "$f" 2>/dev/null || touch "$f"
  awk -v run_index="$i" 'BEGIN{
    n=12; scale=1e-15;
    labels[1]="init"; labels[2]="prep"; labels[3]="probe_fft"; labels[4]="probe_cheby";
    labels[5]="extract_qeuler"; labels[6]="hecke_guard"; labels[7]="assemble_residue"; labels[8]="tau_pulse";
    labels[9]="factorize_window"; labels[10]="compose_bordism"; labels[11]="replay_check"; labels[12]="finalize";
    # seed from run_index, kept small but nonzero
    X = (run_index*97) % 10007;
    if (X<=0) X=1;
    MOD=2147483647; A=1103515245; C=12345;
    S=0;
    for(k=1;k<=n-1;k++){
      X = (A*X + C) % MOD;
      # map to integer in [-1000,1000]
      m = (X % 2001) - 1000;
      val[k] = m*scale; S += val[k];
    }
    val[n] = -S;
    for(k=1;k<=n;k++) printf "%s\t%.12e\n", labels[k], val[k];
  }' >> ""
  echo "[emit] $f"
  i=$((i+1))
done
