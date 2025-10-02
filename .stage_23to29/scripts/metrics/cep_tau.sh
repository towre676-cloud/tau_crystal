#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
seqfile="${1:-.tau_ledger/seq/tau.csv}"; out=".tau_ledger/metrics/cep_tau.json"
[ -s "$seqfile" ] || { echo "{\"CEP_tau\":null,\"error\":\"missing tau.csv\"}" > "$out"; exit 0; }
tmp="$(mktemp)"; awk -F, "NR>1{print $2}" "$seqfile" > "$tmp" || true
awk 'BEGIN{min=1e300; max=-1e300; s=0; s2=0; n=0}{v=$1+0; if(v<min)min=v; if(v>max)max=v; s+=v; s2+=v*v; n++}END{if(n==0){print "{\"CEP_tau\":null}"; exit} mu=s/n; var=(s2/n - mu*mu); if(var<0)var=0; printf("{\"CEP_tau\":{\"n\":%d,\"mean\":%.8f,\"var\":%.8f,\"min\":%.8f,\"max\":%.8f}}\n", n, mu, var, min, max)}' "$tmp" > "$out"
rm -f "$tmp"; echo "$out"
