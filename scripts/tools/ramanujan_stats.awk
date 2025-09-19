BEGIN{FS="\t"; c=0; b=0}
NR>1{p=$1+0; ap=$2+0; bd=2*sqrt(p); if(bd==0)next; c++; if(ap>bd || ap<-bd)b++}
END{printf "%d %d", c, b}
