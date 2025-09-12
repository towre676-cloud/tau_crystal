{ a[NR]=$1+0 } END{ n=NR; for(i=1;i<=n;i++) ord[i]=a[i]; asorti(ord,idx); for(r=1;r<=n;r++) pos[idx[r]]=r; for(i=1;i<=n;i++){ v=(n>1)?(pos[i]-1)/(n-1):0; printf "%.9f\n", v } }
