set -euo pipefail; set +H; umask 022; export LC_ALL=C
IN="${1:-./tmp/qk_corr.txt}"
D="${2:-8}"
LAMBDA="${3:-1e-18}"
NROWS="${4:-0}"
if [ ! -s "$IN" ]; then echo "error: input '$IN' not found or empty" >&2; exit 1; fi
SRC="$IN"
if [ "$NROWS" != "0" ]; then SRC="$(mktemp)"; trap 'rm -f "$SRC"' EXIT; head -n "$NROWS" "$IN" > "$SRC"; fi
echo "[fit] input: $IN  (D=$D, lambda=$LAMBDA, rows=$(wc -l < "$SRC"))"
echo "[fit] head:"; head -n 3 "$SRC" | sed 's/^/[fit]   /'
awk -v D="$D" -v lam="$LAMBDA" '
function abs(x){ return x<0?-x:x }
function pow(x,p,   r){ r=1; for(i=1;i<=p;i++) r*=x; return r }
{ qi[NR]=$1; Ki[NR]=$2; n=NR }
END{
  for(i=1;i<=n;i++){
    q=qi[i]; y=Ki[i]-5.0
    for(d=1; d<=D; d++){ td=pow(q,d); fd[d]=td/(1.0-td) }
    for(j=1;j<=D;j++){
      b[j]+=fd[j]*y
      for(k=1;k<=D;k++) G[j,k]+=fd[j]*fd[k]
    }
  }
  for(j=1;j<=D;j++) G[j,j]+=lam
  for(i=1;i<=D;i++){ for(j=1;j<=D;j++) A[i,j]=G[i,j]; A[i,D+1]=b[i] }
  for(col=1; col<=D; col++){
    piv=col; maxa=abs(A[col,col])
    for(r=col+1; r<=D; r++){ v=abs(A[r,col]); if(v>maxa){ maxa=v; piv=r } }
    if(piv!=col) for(c=col; c<=D+1; c++){ t=A[col,c]; A[col,c]=A[piv,c]; A[piv,c]=t }
    p=A[col,col]; if(p==0){ printf("[warn] singular at col %d\n", col) > "/dev/stderr"; next }
    for(c=col; c<=D+1; c++) A[col,c]/=p
    for(r=1; r<=D; r++) if(r!=col){ f=A[r,col]; if(f!=0) for(c=col; c<=D+1; c++) A[r,c]-=f*A[col,c] }
  }
  for(j=1;j<=D;j++){ a[j]=A[j,D+1]; Nd[j]=a[j]/(j*j*j) }
  sse=0
  for(i=1;i<=n;i++){
    q=qi[i]; y=Ki[i]-5.0; yhat=0
    for(d=1; d<=D; d++){ td=pow(q,d); yhat+=a[d]*(td/(1.0-td)) }
    e=y-yhat; sse+=e*e
  }
  rmse=sqrt(sse/n)
  printf("a_j coefficients (j=1..%d):\n", D)
  for(j=1;j<=D;j++) printf("  a_%d = %.15g\n", j, a[j])
  print ""; print "Instanton numbers N_d (rounded):"
  for(j=1;j<=D;j++) printf("  N_%d ≈ %.0f\n", j, Nd[j])
  printf("\n[fit] rmse = %.6g over %d rows\n", rmse, n)
}' "$SRC"
