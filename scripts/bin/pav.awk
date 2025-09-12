# PAV isotonic regression with diagnostics
BEGIN{ FS="[ \t]+"; OFS="\t" }
{
  t[NR]=$1; nf[NR]=NF; cnt=0; sum=0;
  for(i=2;i<=NF;i++){ data[NR SUBSEP i]=$i; if($i!="NA"){ sum+=$i; cnt++ } }
  y[NR]=(cnt? sum/cnt : (NR>1? y[NR-1] : 0)); w[NR]=(cnt? cnt:1);
  V[NR]=y[NR]; W[NR]=w[NR]; L[NR]=NR; R[NR]=NR; B=NR;
  while(B>1 && V[B-1] > V[B]){
    v=(V[B-1]*W[B-1]+V[B]*W[B])/(W[B-1]+W[B]); V[B-1]=v; W[B-1]+=W[B]; R[B-1]=R[B]; B-- }
}
END{
  # materialize fit
  for(b=1;b<=B;b++){ for(i=L[b]; i<=R[b]; i++){ fit[i]=V[b]; } }
  for(i=1;i<=NR;i++){
    # diagnostics against original rows (ignoring NA)
    s=0; c=0; maxe=0;
    for(j=2;j<=nf[i];j++){
      v=data[i SUBSEP j]; if(v=="NA") continue;
      e=v-fit[i]; if(e<0)e=-e; if(e>maxe)maxe=e; s+= (v-fit[i])*(v-fit[i]); c++
    }
    meen=(c? sqrt(s/c):0); print t[i], fit[i], meen, maxe
  }
}
