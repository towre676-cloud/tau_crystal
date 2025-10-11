#!/usr/bin/env sh
# Usage: ./lrc_csv_discrete.sh N a1 a2 ... ak
# Outputs: N,k,"a1 a2 ...",s_num,s_den,max_num,max_den,OK
# Discrete witness: t ∈ {0,...,N-1}, s = t/N (reduced). OK checks max ≥ 1/(k+1).

N="$1"; shift
A_LIST="$*"

# sanity
[ -z "$N" ] && { echo "err: need N and a_i"; exit 1; }

awk -v N="$N" -v ALIST="$A_LIST" '
function gcd(a,b){a=(a<0?-a:a);b=(b<0?-b:b);while(b){t=a%b;a=b;b=t}return a}
function split_list(str, arr,   n){ gsub(/^[[:space:]]+|[[:space:]]+$/,"",str); n=split(str,arr,/ +/); return n }
BEGIN{
  k = split_list(ALIST, A)
  if(k<1){ print "err: need at least one a_i" > "/dev/stderr"; exit 1 }
  # validate a_i
  for(i=1;i<=k;i++){
    ai = A[i] + 0
    if(ai<=0 || ai>=N){ print "err: each a_i must be in 1..N-1" > "/dev/stderr"; exit 1 }
    for(j=i+1;j<=k;j++) if(ai==A[j]+0){ print "err: a_i must be distinct" > "/dev/stderr"; exit 1 }
  }

  best_dn = -1; best_t = 0

  # discrete times t = 0..N-1
  for(t=0;t<N;t++){
    # compute min_i dist(a_i * t / N, Z) = min_i min(r, N-r)/N, r = (a_i * t) mod N
    min_dn = -1
    for(i=1;i<=k;i++){
      ai = A[i] + 0
      r = (ai * t) % N
      if(r<0) r += N
      dn = r
      if(2*dn > N) dn = N - dn
      if(min_dn<0 || dn < min_dn) min_dn = dn
    }
    if(min_dn > best_dn){ best_dn = min_dn; best_t = t }
  }

  # reduce max = best_dn / N
  g = gcd(best_dn, N); maxN = (g? best_dn/g : best_dn); maxD = (g? N/g : N)

  # s = best_t / N reduced
  g2 = gcd(best_t, N); sN = (g2? best_t/g2 : best_t); sD = (g2? N/g2 : N)

  # threshold check: best_dn/N ≥ 1/(k+1)  <=>  best_dn*(k+1) ≥ N
  OK = (best_dn * (k+1) >= N ? "YES" : "NO")

  # print CSV
  printf "%d,%d,\"", N, k
  for(i=1;i<=k;i++){ printf "%s%s", (i>1?" ":""), A[i] }
  printf "\",%d,%d,%d,%d,%s\n", sN, sD, maxN, maxD, OK
}
'
