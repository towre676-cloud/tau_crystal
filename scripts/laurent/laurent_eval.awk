function K(k,  a,b,t,eps){a=1.0;b=sqrt(1-k*k);eps=1e-15;while(((a>b)?a-b:b-a)>eps){t=(a+b)/2;b=sqrt(a*b);a=t}return (4*atan2(1,1))/(2*a)}
BEGIN{
  pi=4*atan2(1,1); t=theta+0.0; k=sin(t); Kk=K(k); Kp=K(sqrt(1-k*k)); q=exp(-pi*Kp/Kk)
  # Unimodular product phase: phi = 2*sum atan2(q^m sin(m t), 1 - q^m cos(m t))
  phi=0.0; r=q; maxm=2000; tol=1e-15
  for(m=1; m<=maxm && r>tol; m++){ y=r*sin(m*t); x=1.0 - r*cos(m*t); phi+=2.0*atan2(y,x); r*=q }
  re=cos(phi); im=sin(phi)
  printf "%.16g\t%.16g\t%.16g\t%.16g\t%s\n", re, im, Kk, q, seed; exit 0
}
