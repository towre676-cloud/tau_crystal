#!/usr/bin/env python3
import sys
p,a1,a2,a3,a4,a6 = map(int, sys.argv[1:7])
def legendre(a,p):
  a%=p
  if a==0: return 0
  return 1 if pow(a,(p-1)//2,p)==1 else -1
tot=0
for x in range(p):
  b=(a1*x + a3)%p
  xx=x%p; xx2=(xx*xx)%p
  f=( (xx2*xx + a2*xx2 + a4*xx + a6) % p )
  D=( (b*b)%p + (4*f)%p )%p
  tot += legendre(D,p)
print(-tot)
