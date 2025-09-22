#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022
mkdir -p scripts/validation analysis/validation validation/{input,work,logs,receipts,keys}

# ---------- utils ----------
cat > scripts/validation/_util.sh <<'E1'
powmod(){ local a=$1 b=$2 m=$3 r=1; a=$((a%m)); while [ $b -gt 0 ]; do if [ $((b&1)) -eq 1 ]; then r=$(( (r*a)%m )); fi; a=$(( (a*a)%m )); b=$((b>>1)); done; echo $r; }
legendre(){ local a=$1 p=$2; a=$(( (a%p+p)%p )); [ $a -eq 0 ] && { echo 0; return; }; local e=$(( (p-1)/2 )); local t=$(powmod $a $e $p); [ $t -eq 1 ] && echo 1 || echo -1; }
gcd(){ local a=$1 b=$2 t; [ $a -lt 0 ] && a=$((-a)); [ $b -lt 0 ] && b=$((-b)); while [ $b -ne 0 ]; do t=$((a%b)); a=$b; b=$t; done; echo $a; }
egcd(){ local a=$1 b=$2 x0=1 y0=0 x1=0 y1=1 q t; while [ $b -ne 0 ]; do q=$((a/b)); t=$((a-q*b)); a=$b; b=$t; t=$((x0-q*x1)); x0=$x1; x1=$t; t=$((y0-q*y1)); y0=$y1; y1=$t; done; echo "$x0 $y0 $a"; }
invmod(){ local a=$1 m=$2; read x y g < <(egcd $a $m); [ $g -ne 1 ] && { echo -1; return; }; local r=$((x%m)); [ $r -lt 0 ] && r=$((r+m)); echo $r; }
hash_to_z(){ local S="$1" M="$2"; local H; H=$(printf "%s" "$S" | sha256sum | awk '{print $1}'); printf "%d" "$(( 0x${H:0:15} % M ))"; }
E1
chmod +x scripts/validation/_util.sh

# ---------- primes <= 1000 ----------
mkdir -p validation/work
cat > validation/work/primes_1000.txt <<'E2'
2
3
5
7
11
13
17
19
23
29
31
37
41
43
47
53
59
61
67
71
73
79
83
89
97
101
103
107
109
113
127
131
137
139
149
151
157
163
167
173
179
181
191
193
197
199
211
223
227
229
233
239
241
251
257
263
269
271
277
281
283
293
307
311
313
317
331
337
347
349
353
359
367
373
379
383
389
397
401
409
419
421
431
433
439
443
449
457
461
463
467
479
487
491
499
503
509
521
523
541
547
557
563
569
571
577
587
593
599
601
607
613
617
619
631
641
643
647
653
659
661
673
677
683
691
701
709
719
727
733
739
743
751
757
761
769
773
787
797
809
811
821
823
827
829
839
853
857
859
863
877
881
883
887
907
911
919
929
937
941
947
953
967
971
977
983
991
997
E2

# ---------- landmarks -> r (Q^17) ----------
cat > scripts/validation/landmarks_to_r.sh <<'E3'
#!/usr/bin/env bash
set -euo pipefail; set +H
IN="$1"; OUT="$2"; mkdir -p "$(dirname "$OUT")"
awk -F"\t|,| " '{if($1!=""){sx+=$1; sy+=$2; sz+=$3; n++}} END{cx=sx/n; cy=sy/n; cz=sz/n; print cx"\t"cy"\t"cz}' "$IN" > /tmp/ctr.$$
read CX CY CZ < /tmp/ctr.$$
awk -F"\t|,| " -v cx="$CX" -v cy="$CY" -v cz="$CZ" '{if($1!=""){x=$1-cx;y=$2-cy;z=$3-cz; printf("%.9f\t%.9f\t%.9f\n",x,y,z)}}' "$IN" > /tmp/cent.$$
awk -F"\t" 'NR<=20{t+=($1*$1+$2*$2+$3*$3)} END{s=sqrt(t/(NR?NR:1)); if(s==0)s=1; print s}' /tmp/cent.$$ > /tmp/scale.$$
read SC < /tmp/scale.$$
awk -F"\t" -v s="$SC" '{printf("%.9f\t%.9f\t%.9f\n",$1/s,$2/s,$3/s)}' /tmp/cent.$$ > /tmp/norm.$$
awk -F"\t" 'BEGIN{for(i=1;i<=3;i++)a[i]=0} {a[1]+=$1; a[2]+=$2; a[3]+=$3; n++} END{printf("%.9f\t%.9f\t%.9f\n",a[1]/n,a[2]/n,a[3]/n)}' /tmp/norm.$$ > /tmp/f1.$$
printf "%s\n" 1 5 9 13 17 21 25 > /tmp/idx.$$
> /tmp/dots.$$; while read -r idx; do
  awk -F"\t" -v id="$idx" 'NR==id{ax=$1;ay=$2;az=$3} END{print ax"\t"ay"\t"az}' /tmp/norm.$$ > /tmp/a.$$
  read AX AY AZ < /tmp/a.$$
  awk -F"\t" -v ax="$AX" -v ay="$AY" -v az="$AZ" '{d=$1*ax+$2*ay+$3*az; s+=d; c++} END{printf("%.9f\n",s/c)}' /tmp/norm.$$ >> /tmp/dots.$$
done < /tmp/idx.$$
paste -d"\t" /tmp/f1.$$/ /tmp/dots.$$ > /tmp/raw17.$$
awk -F"\t" 'function rat(x,   a,b,g,t){a=int(x*10000+0.5); b=10000; g=a<0?-a:a; while(b&&g){t=g%b; g=b; b=t} if(g==0)g=1; a=int(x*10000+0.5); b=10000; a=int(a/g); b=int(10000/g); return a"/"b} {out=""; for(i=1;i<=NF;i++){if(i>1)out=out"\t"; out=out rat($i)} print out}' /tmp/raw17.$$ > "$OUT"
rm -f /tmp/ctr.$$ /tmp/cent.$$ /tmp/scale.$$ /tmp/norm.$$ /tmp/f1.$$ /tmp/idx.$$ /tmp/a.$$ /tmp/dots.$$ /tmp/raw17.$$
E3
chmod +x scripts/validation/landmarks_to_r.sh

# ---------- r -> curve (A,B) ----------
cat > scripts/validation/r_to_curve.sh <<'E4'
#!/usr/bin/env bash
set -euo pipefail; set +H; . scripts/validation/_util.sh
IN="$1"; OUT="$2"; mkdir -p "$(dirname "$OUT")"
S=$(tr -d "\n\t " < "$IN")
A0=$(hash_to_z "$S:A" 2000001); A=$((A0-1000000))
B0=$(hash_to_z "$S:B" 2000001); B=$((B0-1000000))
disc_zero(){ local A=$1 B=$2; local t=$((4*A*A*A + 27*B*B)); [ $t -eq 0 ]; }
tries=0; while disc_zero "$A" "$B"; do A=$((A+1)); tries=$((tries+1)); [ $tries -gt 10 ] && { B=$((B+1)); tries=0; }; done
printf "%s\n" "A	$A" "B	$B" > "$OUT"
E4
chmod +x scripts/validation/r_to_curve.sh

# ---------- count a_p and build a_n ----------
cat > scripts/validation/count_ap.sh <<'E5'
#!/usr/bin/env bash
set -euo pipefail; set +H; . scripts/validation/_util.sh
CURVE="$1"; OUTP="$2"; OUTN="$3"; PR="validation/work/primes_1000.txt"
read _A A < <(grep -m1 "^A	" "$CURVE"); read _B B < <(grep -m1 "^B	" "$CURVE")
rm -f "$OUTP"; touch "$OUTP"
while read -r p; do
  pts=1
  for ((x=0;x<p;x++)); do
    rhs=$(( ( ((x*x%p)*x)%p + (A%p+p)%p * x )%p )); rhs=$(( (rhs + (B%p+p)%p )%p ))
    chi=$(legendre $rhs $p)
    if [ $chi -eq 0 ]; then pts=$((pts+1)); elif [ $chi -eq 1 ]; then pts=$((pts+2)); fi
  done
  ap=$(( p + 1 - pts ))
  printf "%s\t%s\n" "$p" "$ap" >> "$OUTP"
done < "$PR"
limit=1000; rm -f "$OUTN"; printf "1\t1\n" > "$OUTN"
declare -A AP; while read p v; do AP[$p]=$v; done < "$OUTP"
for ((n=2;n<=limit;n++)); do
  m=$n; an=1; q=2
  while [ $((q*q)) -le $m ]; do
    if [ $((m%q)) -eq 0 ]; then
      k=0; while [ $((m%q)) -eq 0 ]; do m=$((m/q)); k=$((k+1)); done
      if [ -z "${AP[$q]:-}" ]; then aqk=1
      else
        a1=${AP[$q]}
        if [ $k -eq 1 ]; then aqk=$a1
        else a_prev=$a1; a_prev2=1; for ((t=2;t<=k;t++)); do a_now=$(( a1*a_prev - q*a_prev2 )); a_prev2=$a_prev; a_prev=$a_now; done; aqk=$a_prev
        fi
      fi
      an=$((an * aqk))
    fi
    q=$((q+1))
  done
  if [ $m -gt 1 ]; then q=$m; aqk=${AP[$q]:-1}; an=$((an*aqk)); fi
  printf "%s\t%s\n" "$n" "$an" >> "$OUTN"
done
E5
chmod +x scripts/validation/count_ap.sh

# ---------- checks ----------
cat > scripts/validation/checks.sh <<'E6'
#!/usr/bin/env bash
set -euo pipefail; set +H; . scripts/validation/_util.sh
AP="$1"; AN="$2"; AP2="$3"
awk -F"\t" '{if($2 !~ /^-?[0-9]+$/){print "NONINT p="$1" v="$2 > "/dev/stderr"; ok=0}} END{exit ok?0:1}' ok=1 "$AP"
while read -r p a; do
  thr=$(awk -v p="$p" 'BEGIN{printf("%.6f",2*sqrt(p))}')
  abs=$(( a<0?-a:a ))
  awk -v A="$abs" -v T="$thr" 'BEGIN{exit (A<=T)?0:1}' || { echo "RAM_FAIL p="$p" a="$a" thr="$thr >&2; exit 1; }
done < "$AP"
declare -A ANV; while read -r n a; do ANV[$n]=$a; done < "$AN"
for ((m=2;m<=50;m++)); do for ((n=2;n<=50;n++)); do mn=$((m*n)); if [ $mn -le 1000 ]; then g=$(gcd $m $n); if [ $g -eq 1 ]; then am=${ANV[$m]:-0}; an=${ANV[$n]:-0}; amn=${ANV[$mn]:-999999999}; [ $((am*an)) -eq $amn ] || { echo "MULT_FAIL m="$m" n="$n >&2; exit 1; }; fi; fi; done; done
join -t "	" -j1 <(sort -n "$AP") <(sort -n "$AP2") | awk -F"\t" '{if($2!=$3){print "STAB_FAIL p="$1" a1="$2" a2="$3 > "/dev/stderr"; exit 1}}'
E6
chmod +x scripts/validation/checks.sh

# ---------- signing & packing ----------
cat > scripts/validation/sign_dataset.sh <<'E7'
#!/usr/bin/env bash
set -euo pipefail; set +H
BIN="$1"; OUT="$2"; mkdir -p "$(dirname "$OUT")"
HASH=$(sha256sum "$BIN" | awk '{print $1}')
if command -v openssl >/dev/null 2>&1; then
  [ -f validation/keys/ed25519_sk.pem ] || openssl genpkey -algorithm ED25519 -out validation/keys/ed25519_sk.pem >/dev/null 2>&1
  openssl pkey -in validation/keys/ed25519_sk.pem -pubout -out validation/keys/ed25519_pk.pem >/dev/null 2>&1
  openssl dgst -sha256 -sign validation/keys/ed25519_sk.pem -out validation/keys/sig.bin "$BIN"
  SIG=$(xxd -p -c 1000 validation/keys/sig.bin)
  PK=$(awk 'BEGIN{ORS=""} {gsub(/\r/,""); print}' validation/keys/ed25519_pk.pem)
else SIG="NO_OPENSSL"; PK="NO_OPENSSL"; fi
printf "%s\n" "time	$(date -u +%FT%TZ)" "sha256	$HASH" "sig_ed25519_hex	$SIG" "pubkey_pem	$PK" > "$OUT"
echo "$OUT"
E7
chmod +x scripts/validation/sign_dataset.sh

cat > scripts/validation/pack_dataset.sh <<'E8'
#!/usr/bin/env bash
set -euo pipefail; set +H
LIST="$1"; OUTBIN="$2"; RECEIPT="$3"
rm -f "$OUTBIN" "$RECEIPT"; touch "$OUTBIN"
while IFS= read -r row; do [ -z "$row" ] && continue; printf "%s\n" "$row" >> "$OUTBIN"; done < "$LIST"
H=$(sha256sum "$OUTBIN" | awk '{print $1}')
printf "%s\n" "time	$(date -u +%FT%TZ)" "dataset	$OUTBIN" "sha256	$H" > "$RECEIPT"
printf "%s\n" "op_return_hex	6a20$H" "broadcast_instructions	use your wallet to push OP_RETURN with this data" >> "$RECEIPT"
echo "$OUTBIN"
E8
chmod +x scripts/validation/pack_dataset.sh

# ---------- per-face pipeline ----------
cat > scripts/validation/face_to_ap.sh <<'E9'
#!/usr/bin/env bash
set -euo pipefail; set +H
IN="$1"; ID="$2"; WORK="validation/work/$ID"; mkdir -p "$WORK"
R="$WORK/r.tsv"; CUR="$WORK/curve.tsv"; AP1="$WORK/a_p.tsv"; AN1="$WORK/a_n.tsv"; AP2="$WORK/a_p_pass2.tsv"
bash scripts/validation/landmarks_to_r.sh "$IN" "$R"
bash scripts/validation/r_to_curve.sh "$R" "$CUR"
bash scripts/validation/count_ap.sh "$CUR" "$AP1" "$AN1"
bash scripts/validation/count_ap.sh "$CUR" "$AP2" "$WORK/a_n_pass2.tsv"
set +e; bash scripts/validation/checks.sh "$AP1" "$AN1" "$AP2"; OK=$?; set -e
read _A A < <(grep "^A	" "$CUR"); read _B B < <(grep "^B	" "$CUR")
RFLAT=$(tr "\n" " " < "$R" | tr "\t" " " | sed "s/  */ /g; s/ $//")
HASH=$(sha256sum "$AP1" | awk '{print $1}')
ROW="id=$ID|r=$RFLAT|A=$A|B=$B|hash_ap=$HASH|ok=$OK"
printf "%s\n" "$ROW" > "$WORK/row.txt"
echo "$WORK/row.txt"
E9
chmod +x scripts/validation/face_to_ap.sh

# ---------- experiment runner ----------
cat > scripts/validation/run_experiment.sh <<'E10'
#!/usr/bin/env bash
set -euo pipefail; set +H
IN_DIR="validation/input"; LIST="validation/work/dataset_rows.txt"; mkdir -p "$(dirname "$LIST")"; : > "$LIST"
i=0; for f in "$IN_DIR"/*.tsv; do [ -e "$f" ] || continue; i=$((i+1)); id=$(printf "face%03d" "$i"); rowfile=$(bash scripts/validation/face_to_ap.sh "$f" "$id"); cat "$rowfile" >> "$LIST"; [ $i -ge 50 ] && break; done
[ $i -ge 50 ] || echo "WARNING: only $i faces found; proceeding."
OUTBIN="analysis/validation/SIGNED_DATASET.bin"; RECEIPT="analysis/validation/SIGNED_DATASET.receipt.tsv"
mkdir -p analysis/validation
bash scripts/validation/pack_dataset.sh "$LIST" "$OUTBIN" "$RECEIPT" >/dev/null
bash scripts/validation/sign_dataset.sh "$OUTBIN" "analysis/validation/corridor.receipt.tsv" >/dev/null
printf "%s\n" "dataset_bin	$OUTBIN" "receipt	$RECEIPT" >> "analysis/validation/corridor.receipt.tsv"
printf "%s\n" "DONE	$(date -u +%FT%TZ)" >> "analysis/validation/corridor.receipt.tsv"
echo "SIGNED_DATASET at $OUTBIN"
E10
chmod +x scripts/validation/run_experiment.sh

# ---------- normalizer ----------
cat > validation/work/normalize_one.sh <<'E11'
#!/usr/bin/env bash
set -euo pipefail; set +H
IN="$1"; OUT="$2"; ext="${IN##*.}"; ext="${ext,,}"
case "$ext" in
  csv) awk -F"," '{printf("%s\t%s\t%s\n",$1,$2,$3)}' "$IN" ;;
  tsv|txt) awk '{gsub(/[ ,]+/,"\t"); print $0}' "$IN" ;;
  pts) awk '/\{/{inb=1; next} /\}/{inb=0} inb{print}' "$IN" | awk '{if(NF==2) printf("%s\t%s\t0\n",$1,$2); else printf("%s\t%s\t%s\n",$1,$2,$3)}' ;;
  *) echo "Unsupported ext: ${ext}" >&2; exit 6 ;;
esac |
awk -F"\t" 'NF>=2 && $1!~ /^#/ {if(NF==2) printf("%s\t%s\t0\n",$1,$2); else printf("%s\t%s\t%s\n",$1,$2,$3)}' > "$OUT.tmp"
lines=$(wc -l < "$OUT.tmp" | tr -d " ")
[ "$lines" -eq 68 ] || { rm -f "$OUT.tmp"; exit 7; }
mv "$OUT.tmp" "$OUT"; echo "$OUT"
E11
chmod +x validation/work/normalize_one.sh

# ---------- harvest LS3D-W to validation/input ----------
[ -n "${LS3D_DIR:-}" ] || { echo "LS3D_DIR env var not set"; exit 2; }
[ -d "$LS3D_DIR" ] || { echo "LS3D_DIR not found: $LS3D_DIR"; exit 2; }
CAND="validation/work/candidates.txt"
find "$LS3D_DIR" -type f \( -iname '*.pts' -o -iname '*.csv' -o -iname '*.tsv' -o -iname '*.txt' \) 2>/dev/null | sort -u > "$CAND"
mkdir -p validation/input
i=0
while IFS= read -r f; do
  [ $i -ge 50 ] && break
  out="validation/input/face$(printf "%03d" $((i+1))).tsv"
  if validation/work/normalize_one.sh "$f" "$out" >/dev/null 2>&1; then i=$((i+1)); fi
done < "$CAND"
cnt=$(ls -1 validation/input/face*.tsv 2>/dev/null | wc -l | tr -d ' ' || echo 0)
[ "$cnt" -ge 1 ] || { echo "No usable LS3D-W files normalized."; exit 4; }
[ "$cnt" -ge 50 ] || echo "NOTE: only $cnt faces prepared (need 50 for prereg). Proceeding."

# ---------- run experiment ----------
bash scripts/validation/run_experiment.sh

# show receipts
echo "Artifacts:"
echo "  analysis/validation/SIGNED_DATASET.bin"
echo "  analysis/validation/SIGNED_DATASET.receipt.tsv"
echo "  analysis/validation/corridor.receipt.tsv"
grep -E '^op_return_hex' analysis/validation/SIGNED_DATASET.receipt.tsv || true
