#!/usr/bin/env sh
# Usage: ./lrc_tiny.sh N a1 a2 ... ak
# Computes max_{s in T} f(s) and a witness s where
#   f(s) = min_i dist(a_i * s, Z),  s = m/d with d in {a_i} ∪ {|a_i ± a_j|}
# Pure POSIX sh + awk, integer-safe.

if [ "$#" -lt 2 ]; then
  echo "Usage: $0 N a1 a2 ... ak" >&2
  exit 1
fi

N="$1"; shift
A_LIST="$*"

awk -v A_LIST="$A_LIST" '
function gcd(a,b){a=a<0?-a:a; b=b<0?-b:b; while(b){t=a%b; a=b; b=t} return a}
function abs(x){return x<0?-x:x}

BEGIN{
  split(A_LIST, a, /[[:space:]]+/); k=0
  for(i in a){ if(a[i]!=""){k++; ai[k]=a[i]+0} }
  if(k<1){ print "need at least one a_i"; exit 1 }

  # build denominators: {a_i} ∪ {|a_i ± a_j|>0}
  delete D
  for(i=1;i<=k;i++){ if(ai[i]>0) D[ai[i]]=1 }
  for(i=1;i<=k;i++) for(j=i+1;j<=k;j++){
    d=ai[i]+ai[j]; if(d>0) D[d]=1
    d=abs(ai[i]-ai[j]); if(d>0) D[d]=1
  }

  best_n=0; best_d=1; best_m=0; best_ds=1

  # iterate candidates s = m/d (m=0..d-1) for each denom d
  for(dstr in D){
    d = dstr + 0
    if(d<=0) continue
    for(m=0;m<d;m++){
      # f(s) numerator over denom d
      min_n = d
      for(i=1;i<=k;i++){
        r = (ai[i]*m) % d; if(r<0) r+=d
        rn = r; if(rn > d-rn) rn = d-rn
        if(rn < min_n){ min_n = rn; if(min_n==0) break }
      }
      # compare min_n/d vs best_n/best_d
      if( (min_n*best_d) > (best_n*d) ){
        best_n=min_n; best_d=d; best_m=m; best_ds=d
      }
    }
  }

  # reduce max value best_n/best_d
  if(best_n==0){ out_n=0; out_d=1 } else { g=gcd(best_n,best_d); out_n=best_n/g; out_d=best_d/g }

  # reduce witness s = best_m/best_ds
  if(best_m==0){ s_n=0; s_d=1 } else { g2=gcd(best_m,best_ds); s_n=best_m/g2; s_d=best_ds/g2 }

  # distances at witness
  printf "max f(s) = %d/%d at s = %d/%d\n", out_n,out_d, s_n,s_d
  printf "distances at witness: ["
  for(i=1;i<=k;i++){
    r = (ai[i]*best_m) % best_ds; if(r<0) r+=best_ds
    dn = r; if(dn > best_ds - dn) dn = best_ds - dn
    if(dn==0){ printf (i==1?" ":"; ") "0" }
    else { g3=gcd(dn,best_ds); printf (i==1?" ":"; ") "%d/%d", dn/g3, best_ds/g3 }
  }
  print " ]"
  thr_n=1; thr_d=k+1
  if(out_n*thr_d >= thr_n*out_d) ok="YES"; else ok="NO"
  printf "threshold 1/%d -> LRC satisfied? %s\n", k+1, ok
}
'
