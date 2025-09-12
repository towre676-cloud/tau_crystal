# PAV isotonic regression for fused τ
BEGIN{ FS="[ \t]+"; OFS="\t" }
# Input: rows "t s1 s2 ...", missing as "NA". Output: t fused mean_err max_abs_err
{
  t[NR]=$1; n=0; sum=0; cnt=0;
  for(i=2;i<=NF;i++){ if($i!="NA"){ sum+=$i; cnt++ } }
  if(cnt==0){ y[NR]= (NR>1? y[NR-1] : 0); w[NR]=1 } else { y[NR]=sum/cnt; w[NR]=cnt }
  blk_v[NR]=y[NR]; blk_w[NR]=w[NR]; blk_l[NR]=NR; blk_r[NR]=NR; B=NR;
  while(B>1 && blk_v[B-1] > blk_v[B]){
    v=(blk_v[B-1]*blk_w[B-1] + blk_v[B]*blk_w[B])/(blk_w[B-1]+blk_w[B]);
    blk_v[B-1]=v; blk_w[B-1]+=blk_w[B]; blk_r[B-1]=blk_r[B]; B--; }
}
END{
  fit_idx=1; for(b=1;b<=B;b++){ for(i=blk_l[b]; i<=blk_r[b]; i++){ fit[i]=blk_v[b]; } }
  for(i=1;i<=NR;i++){
    # recompute mean and max deviation for diagnostics
    sum=0; cnt=0; maxe=0;
    for(j=2;j<=NF;j++){ if(data[i,j]!="NA"){ e=(data[i,j]-fit[i]); if(e<0)e=-e; if(e>maxe)maxe=e; sum+= (data[i,j]-fit[i])*(data[i,j]-fit[i]); cnt++; } }
    meen=(cnt? sqrt(sum/cnt) : 0); print t[i], fit[i], meen, maxe;
  }
}
function store(){ for(i=2;i<=NF;i++) data[NR,i]=$i }
