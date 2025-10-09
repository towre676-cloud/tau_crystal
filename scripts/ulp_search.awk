# ULP bounded-denominator search with MDL/BIC
# k<=2 nonzeros, |v|<=0.5; emits BUCKET rows only (driver picks REP).
# -v inputs: Y0,SIG0,DMAX0,PMAX0,MDL0, Z0v..Z4v

function bic(eps,k,maxq, nobs,chi2){
  nobs=5
  chi2 = (SIG>0 ? (eps*eps)/(SIG*SIG) : 1e12*eps*eps)
  return chi2 + k*log(nobs) + (MDL+0.0)*maxq
}
function add(r0,r1,r2,r3,r4,eps,k,maxq, B,z,chi2,L1){
  B=bic(eps,k,maxq)
  if (B < best-1e-15) {best=B; m=0}
  if (B <= best+2+1e-15) {
    S[m,0]=r0; S[m,1]=r1; S[m,2]=r2; S[m,3]=r3; S[m,4]=r4
    S[m,5]=eps; S[m,6]=k;  S[m,7]=maxq; SB[m]=B
    z   = (SIG>0 ? eps/SIG : 0); chi2 = z*z
    L1  = (r0<0?-r0:r0)+(r1<0?-r1:r1)+(r2<0?-r2:r2)+(r3<0?-r3:r3)+(r4<0?-r4:r4)
    SZ[m]=z; SCHI[m]=chi2; SL1[m]=L1
    m++
  }
}
# NOTE: parameters renamed to avoid shadowing globals
function sc1(ii,  q,p,v,yhat,r0,r1,r2,r3,r4){
  for(q=1;q<=DMAX;q++){
    for(p=-PMAX;p<=PMAX;p++){
      if(p==0) continue
      v=p/q; if (v<-0.5 || v>0.5) continue
      r0=r1=r2=r3=r4=0
      (ii==0)?r0=v:(ii==1)?r1=v:(ii==2)?r2=v:(ii==3)?r3=v:r4=v
      yhat=r0*Z0+r1*Z1+r2*Z2+r3*Z3+r4*Z4
      add(r0,r1,r2,r3,r4, Y-yhat, 1, q)
    }
  }
}
# NOTE: parameters renamed to avoid shadowing globals
function sc2(ii,jj,  q1,p1,q2,p2,v1,v2,yhat,k,maxq,r0,r1,r2,r3,r4){
  for(q1=1;q1<=DMAX;q1++){
    for(p1=-PMAX;p1<=PMAX;p1++){
      for(q2=1;q2<=DMAX;q2++){
        for(p2=-PMAX;p2<=PMAX;p2++){
          if(p1==0 && p2==0) continue
          v1=p1/q1; v2=p2/q2
          if (v1<-0.5 || v1>0.5 || v2<-0.5 || v2>0.5) continue
          r0=r1=r2=r3=r4=0
          (ii==0)?r0=v1:(ii==1)?r1=v1:(ii==2)?r2=v1:(ii==3)?r3=v1:r4=v1
          (jj==0)?r0=v2:(jj==1)?r1=v2:(jj==2)?r2=v2:(jj==3)?r3=v2:r4=v2
          yhat=r0*Z0+r1*Z1+r2*Z2+r3*Z3+r4*Z4
          k=(p1!=0)+(p2!=0); maxq=(q1>q2?q1:q2)
          add(r0,r1,r2,r3,r4, Y-yhat, k, maxq)
        }
      }
    }
  }
}

BEGIN{
  Y=Y0+0.0; SIG=SIG0+0.0; DMAX=int(DMAX0+0); PMAX=int(PMAX0+0); MDL=MDL0+0.0
  Z0=Z0v+0.0; Z1=Z1v+0.0; Z2=Z2v+0.0; Z3=Z3v+0.0; Z4=Z4v+0.0
  best=1e99; m=0

  # explore 1- and 2-term sparse rationals
  for(i=0;i<5;i++) sc1(i)
  for(i=0;i<5;i++) for(j=i+1;j<5;j++) sc2(i,j)

  # emit bucket rows
  for(i=0;i<m;i++)
    printf "BUCKET\t%.12g\t%.12g\t%.12g\t%.12g\t%.12g\t%.12g\t%.12g\t%.12g\t%d\t%d\t%.12g\t%.12g\n",
           S[i,0],S[i,1],S[i,2],S[i,3],S[i,4], S[i,5], SZ[i], SCHI[i], S[i,6], S[i,7], SL1[i], SB[i]
}
