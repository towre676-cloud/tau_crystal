
#!/usr/bin/env bash
# runner.sh — PF dual -> fit c -> S∘T^c -> intersect(u) -> feed/cert/diff with logs + parsed roots
set -euo pipefail; set +H; umask 022; export LC_ALL=C

cd "$HOME/Desktop/tau_crystal/tau_crystal" || exit 1
REPO="$(pwd)"

mkdir -p .tau_ledger/logs

# CRLF hygiene
for f in nekrasov.tsv picard_fuchs.tsv scripts/*.sh; do
  [ -f "$f" ] || continue
  sed -i 's/\r$//' "$f" 2>/dev/null || true
done

# scripts present and parse
for f in scripts/sw_any_feed.sh scripts/sw_any_certify.sh scripts/sw_any_diff_first.sh; do
  [ -f "$f" ] || { echo "[FATAL] missing $f"; exit 2; }
  chmod +x "$f" || true
done
bash -n scripts/sw_any_feed.sh scripts/sw_any_certify.sh scripts/sw_any_diff_first.sh

# --- PF dual pair from picard_fuchs.tsv ---
# sort numerically by first column (u); no $'\t' to avoid quoting pain
sort -n -k1,1 picard_fuchs.tsv > .tau_ledger/pf_sorted.tsv
awk -v OFS="\t" '
function canon(s){gsub(/[^A-Za-z0-9_]+/,"_",s); return tolower(s)}
function idx(name,i){name=canon(name); for(i=1;i<=NF;i++) if(canon($i)==name) return i; return -1}
NR==1{
  iu=idx("u"); ia=idx("a"); ia1=idx("a1"); ia2=idx("a2"); ip2=idx("p2"); ip1=idx("p1"); ip0=idx("p0"); iseed=idx("seed");
  if(iu<0||ia<0||ia1<0||ia2<0||ip2<0||ip1<0||ip0<0){ print "[FATAL] picard_fuchs.tsv header missing fields" > "/dev/stderr"; exit 2 }
  print "u","a","a1","a2","aD","aD1","aD2","p2","p1","p0" (iseed>0? "\tseed": ""); next
}
{
  u=$iu+0; a=$ia+0; a1=$ia1+0; a2=$ia2+0; p2=$ip2+0; p1=$ip1+0; p0=$ip0+0; seed=(iseed>0?$iseed:"");
  vp  = (a!=0 ? 1.0/(a*a) : 0.0);
  vpp = (a!=0 ? -2.0*a1/((a*a)*a) : 0.0);
  if(NR==2){ v=0.0; } else { v += 0.5*(vp_prev+vp)*(u-u_prev); }
  aD  = a*v;
  aD1 = a1*v + a*vp;
  aD2 = a2*v + 2.0*a1*vp + a*vpp;
  printf "%.15g\t%.16g\t%.16g\t%.16g\t%.16g\t%.16g\t%.16g\t%.16g\t%.16g\t%.16g", \
         u, a, a1, a2, aD, aD1, aD2, p2, p1, p0;
  if(iseed>0) printf "\t%s", seed;
  printf "\n";
  u_prev=u; vp_prev=vp;
}
' .tau_ledger/pf_sorted.tsv > pf_pair.tsv
rm -f .tau_ledger/pf_sorted.tsv

# --- fit c on overlapping u: a_N ≈ aD + c*a ---
c="$(
  awk 'FNR==NR && NR>1{u=sprintf("%.15g",$1); a[u]=$2; aD[u]=$5; next}
       NR>1       {u=sprintf("%.15g",$1); if(u in a){ sAA+=a[u]*a[u]; sAx+=a[u]*( $2 - aD[u] ); }}
       END{ if(sAA>0) printf("%.16f\n", sAx/sAA) }' pf_pair.tsv nekrasov.tsv
)"
[ -n "${c:-}" ] || { echo "[FATAL] could not fit c (no overlapping u)"; exit 2; }
echo "[INFO] fitted c = $c"

# --- EM mix to S∘T^c ---
awk -v OFS="\t" -v A="1.0" -v B="$c" '
function canon(s){gsub(/[^A-Za-z0-9_]+/,"_",s); return tolower(s)}
function idx(name,i){name=canon(name); for(i=1;i<=NF;i++) if(canon($i)==name) return i; return -1}
NR==1{
  iu=idx("u"); ia=idx("a"); ia1=idx("a1"); ia2=idx("a2");
  iD=idx("aD"); iD1=idx("aD1"); iD2=idx("aD2");
  ip2=idx("p2"); ip1=idx("p1"); ip0=idx("p0"); iseed=idx("seed");
  if(iu<0||ia<0||ia1<0||ia2<0||iD<0||iD1<0||iD2<0||ip2<0||ip1<0||ip0<0){
    print "[FATAL] pf_pair.tsv header missing fields" > "/dev/stderr"; exit 2
  }
  print "u","a","a1","a2","p2","p1","p0" (iseed>0? "\tseed": ""); next
}
{
  u=$iu+0; a=$ia+0; a1=$ia1+0; a2=$ia2+0; aD=$iD+0; aD1=$iD1+0; aD2=$iD2+0;
  p2=$ip2+0; p1=$ip1+0; p0=$ip0+0; seed=(iseed>0?$iseed:"");
  an  = A*aD  + B*a;
  an1 = A*aD1 + B*a1;
  an2 = A*aD2 + B*a2;
  printf "%.15g\t%.16g\t%.16g\t%.16g\t%.16g\t%.16g\t%.16g", u, an, an1, an2, p2, p1, p0;
  if(iseed>0) printf "\t%s", seed;
  printf "\n";
}
' pf_pair.tsv > pf_S_Tc.tsv

# --- align both files to the exact intersection of u-keys ---
awk 'NR==1{next} {u=sprintf("%.15g",$1); k[u]=1} END{for(x in k) print x}' pf_S_Tc.tsv | sort -n > .tau_ledger/pf.keys
awk 'NR==1{next} {u=sprintf("%.15g",$1); k[u]=1} END{for(x in k) print x}' nekrasov.tsv | sort -n > .tau_ledger/nek.keys
comm -12 .tau_ledger/pf.keys .tau_ledger/nek.keys > .tau_ledger/u.inter

awk 'FNR==NR{K[$1]=1; next} NR==1{print; next} {key=sprintf("%.15g",$1); if(K[key]) print}' \
  .tau_ledger/u.inter nekrasov.tsv > nekrasov_int.tsv
awk 'FNR==NR{K[$1]=1; next} NR==1{print; next} {key=sprintf("%.15g",$1); if(K[key]) print}' \
  .tau_ledger/u.inter pf_S_Tc.tsv > pf_S_Tc_int.tsv

n_int="$(awk 'END{print NR-1}' nekrasov_int.tsv 2>/dev/null || printf 0)"
echo "[INFO] intersection size = ${n_int}"
[ "$n_int" -gt 0 ] || { echo "[FATAL] empty u-intersection; cannot diff"; exit 2; }

# --- feed/cert/diff on the aligned pair ---
TS="$(date -u +%Y%m%dT%H%M%SZ)"
OA=".tau_ledger/logs/FEED_NEK_${TS}.out"; EA=".tau_ledger/logs/FEED_NEK_${TS}.err"
OB=".tau_ledger/logs/FEED_PFSTC_${TS}.out"; EB=".tau_ledger/logs/FEED_PFSTC_${TS}.err"
OC=".tau_ledger/logs/CERT_${TS}.out";     EC=".tau_ledger/logs/CERT_${TS}.err"
OD=".tau_ledger/logs/DIFF_${TS}.out";     ED=".tau_ledger/logs/DIFF_${TS}.err"

set +e
bash -x scripts/sw_any_feed.sh    nekrasov_int.tsv  nekrasov_int  swpf0 1>"$OA" 2>"$EA" </dev/null; RC_A=$?
bash -x scripts/sw_any_feed.sh    pf_S_Tc_int.tsv   pf_S_Tc_int  swpf0 1>"$OB" 2>"$EB" </dev/null; RC_B=$?
bash -x scripts/sw_any_certify.sh nekrasov_int.tsv pf_S_Tc_int.tsv nekrasov_int pf_S_Tc_int swpf0 1>"$OC" 2>"$EC" </dev/null; RC_C=$?
bash -x scripts/sw_any_diff_first.sh nekrasov_int.tsv pf_S_Tc_int.tsv swpf0 1>"$OD" 2>"$ED" </dev/null; RC_D=$?
set -e

echo
echo "=== FEED_NEK : STDOUT ===";  sed -n '1,200p' "$OA" || true
echo
echo "=== FEED_PFSTC: STDOUT ==="; sed -n '1,200p' "$OB" || true
echo
echo "=== CERT     : STDOUT ===";  sed -n '1,200p' "$OC" || true
echo
echo "=== DIFF     : STDOUT ===";  sed -n '1,200p' "$OD" || true

echo
echo "=== ROOTS & RECEIPTS (parsed) ==="
root_nek="$(awk '$1=="ROOT"{print $2; exit}'    "$OA" 2>/dev/null)";     root_nek="${root_nek:-<none>}"
rcpt_nek="$(awk '$1=="RECEIPT"{print $2; exit}'  "$OA" 2>/dev/null)";     rcpt_nek="${rcpt_nek:-<none>}"
root_pf="$(awk  '$1=="ROOT"{print $2; exit}'    "$OB" 2>/dev/null)";      root_pf="${root_pf:-<none>}"
rcpt_pf="$(awk  '$1=="RECEIPT"{print $2; exit}'  "$OB" 2>/dev/null)";     rcpt_pf="${rcpt_pf:-<none>}"
printf '[ROOT nekrasov_int]     %s\n' "$root_nek"
printf '[RECEIPT nekrasov_int] %s\n' "$rcpt_nek"
printf '[ROOT pf_S_Tc_int]      %s\n' "$root_pf"
printf '[RECEIPT pf_S_Tc_int]  %s\n' "$rcpt_pf"

echo
echo "[STATUS] FEED_NEK=$RC_A FEED_PFSTC=$RC_B CERT=$RC_C DIFF=$RC_D"

