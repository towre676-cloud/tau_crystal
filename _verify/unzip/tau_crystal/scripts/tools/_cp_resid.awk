function q(x,s){ return (x>=0)?int(x*s+0.5):-int(-x*s+0.5) }
function isnum(s){ return (s ~ /^[-+]?[0-9]*\.?[0-9]+([eE][-+]?[0-9]+)?$/) }
BEGIN{OFS="\t"; scale=1e9; maxd=0; pairs=0}
NR==1 && (!isnum($t) || !isnum($v)) { next }
{ th=$t+0; val=$v+0; key=q(th,scale); sum[key]+=val; cnt[key]++ }
END{
  for(k in cnt){ if(k>=0){ m=-k; if(m in cnt){
    a=sum[k]/cnt[k]; b=sum[m]/cnt[m]; d=a-b; if(d<0)d=-d
    if(d>maxd)maxd=d; pairs++
  } } }
  pass=(pairs>0 ? (maxd<=eps?1:0) : (strict?0:1))
  printf "residual\t%.12g\n", maxd
  printf "epsilon\t%.12g\n", eps
  printf "pairs\t%d\n", pairs
  printf "pass\t%d\n", pass
  exit (pass?0:4)
}
