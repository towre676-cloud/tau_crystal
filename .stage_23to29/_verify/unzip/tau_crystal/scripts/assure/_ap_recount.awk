function powmod(a,e,m){r=1;a%=m;if(a<0)a+=m;while(e>0){if(e%2==1)r=(r*a)%m;a=(a*a)%m;e=int(e/2)}return r}
function legendre(a,p){a%=p;if(a==0)return 0; t=powmod(a,(p-1)/2,p); return (t==p-1)?-1:t}
BEGIN{
  tot=0;
  for(x=0;x<p;x++){
    b=(a1*x + a3)%p; if(b<0)b+=p;
    xx=x%p; xx2=(xx*xx)%p;
    f=( ( (xx2*xx)%p + (a2*xx2)%p + (a4*xx)%p + (a6%p) )%p ); if(f<0)f+=p;
    D=( (b*b)%p + (4*f)%p )%p; if(D<0)D+=p;
    tot += legendre(D,p);
  }
  print -tot;
}
