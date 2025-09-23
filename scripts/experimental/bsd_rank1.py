import io,json,math,sys,cmath,os
csv_path=".tau_ledger/seq/tau.csv"
out=".tau_ledger/experimental/bsd_rank1.json"

def dft(x):
    N=len(x); X=[0j]*N
    for k in range(N):
        s=0j
        for n in range(N):
            s += x[n]*cmath.exp(-2j*math.pi*k*n/N)
        X[k]=s
    return X

def idft(X):
    N=len(X); x=[0j]*N
    for n in range(N):
        s=0j
        for k in range(N):
            s += X[k]*cmath.exp(2j*math.pi*k*n/N)
        x[n]=s/N
    return x

def spectral_derivatives(y):
    N=len(y); Y=dft([complex(v,0.0) for v in y])
    w=[2*math.pi*k/N for k in range(N)]
    Y1=[1j*w[k]*Y[k] for k in range(N)]
    Y2=[-(w[k]**2)*Y[k] for k in range(N)]
    f=idft(Y); f1=idft(Y1); f2=idft(Y2)
    return f,f1,f2

