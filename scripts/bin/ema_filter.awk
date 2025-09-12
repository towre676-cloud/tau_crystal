BEGIN{ FS="[ \t]+"; OFS="\t" }
{ if(NR==1){tau=$2; print $1, tau; next} z=$2; for(i=1;i<=K;i++){ tau = W*tau + (1.0-W)*z } print $1, tau }
