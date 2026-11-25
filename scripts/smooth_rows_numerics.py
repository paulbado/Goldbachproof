#!/usr/bin/env python3
"""docs/tex/localized-buchstab-wall-ii.tex §8: T(P,N)/#I and |S|/P for sampled N (P-smooth rows vs P-smooth integers in [N-P,N])."""
import numpy as np, math
def spf_upto(n):
    s=np.arange(n+1,dtype=np.int64)
    for i in range(2,int(n**.5)+1):
        if s[i]==i: s[i*i::i]=np.minimum(s[i*i::i],i)
    return s
def gpf(n,spf):
    g=1
    while n>1: p=spf[n]; g=max(g,p); n//=p
    return g
def rho(K): return 1-math.log(K)
for P in (1009,3001):
    LIM=int(P**1.77)+10; spf=spf_upto(LIM)
    ps=[q for q in range(3,P+1) if spf[q]==q]
    rng=np.random.default_rng(5)
    for K in (5/3,1.70,1.75):
        rs=[]
        for _ in range(200):
            N=2*int(rng.integers(int(P**K)//2,int(P**K*1.02)//2))
            T=sum(1 for l in ps if gpf(N-l,spf)<=P)
            S=sum(1 for n in range(N-P,N+1) if gpf(n,spf)<=P)
            rs.append((T/len(ps), S/(P+1)))
        a=np.array(rs)
        print(f"P={P} K={K:.3f}: rho={rho(K):.3f}  T/#I mean={a[:,0].mean():.3f} max={a[:,0].max():.3f}  |S|/P mean={a[:,1].mean():.3f}")
