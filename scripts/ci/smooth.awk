{ x[NR]=$1+0 } END{ ema=0; s=0; for(i=1;i<=NR;i++){ s+=x[i]; if(i>K) s-=x[i-K]; m=s/((i<K)?i:K); ema=W*ema+(1-W)*m; printf "%.9f\n", ema } }
