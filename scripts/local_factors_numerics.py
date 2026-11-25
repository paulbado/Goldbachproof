#!/usr/bin/env python3
"""docs/tex/localized-buchstab-wall-ii.tex §8.4-8.9: empirical vs model local factors F_N = prod (1-g_N(p))/(1-1/p) for S = {n in [N-P,N] : P^+(n) < P}."""
import numpy as np, math
def spf_upto(n):
    s=np.arange(n+1,dtype=np.int64)
    for i in range(2,int(n**.5)+1):
        if s[i]==i: s[i*i::i]=np.minimum(s[i*i::i],i)
    return s
rho=lambda u: 1-math.log(u) if 1<=u<=2 else (1.0 if u<1 else None)
P=3001; K=5/3; LIM=int(P**1.7)+10; spf=spf_upto(LIM)
def gpf(n):
    g=1
    while n>1: p=spf[n]; g=max(g,p); n//=p
    return g
ps=[q for q in range(2,P) if spf[q]==q]; I=[q for q in ps if q>=3]+([P] if spf[P]==P else [])
rng=np.random.default_rng(7); out=[]
for _ in range(120):
    N=2*int(rng.integers(int(P**K)//2,int(P**K*1.02)//2))
    S=[n for n in range(N-P+1,N+1) if gpf(n)<P]      # strict: P^+(n) < P
    T=sum(1 for l in I if gpf(N-l)<P)
    # empirical local factor over p < 60, and model factor with c_p = rho(K-beta)/rho(K)
    Femp=1.0; Fmod=1.0; L=math.log(P)
    for p in [q for q in ps if q<60]:
        gemp=sum(1 for n in S if (N-n)%p==0)/len(S)
        Femp*= (1-gemp)/(1-1/p)
        c=rho(K-math.log(p)/L)/rho(K)
        gm = c/p if N%p==0 else (1-c/p)/(p-1)
        Fmod*= (1-gm)/(1-1/p)
    pred=len(S)*Femp/L*(1/ (1))   # expected T ~ |S| * F / log P  (prime density ~1/log P)
    out.append((T, len(S)*Femp/math.log(P), len(S)*Fmod/math.log(P), Femp, Fmod, N%3==0))
a=np.array(out,dtype=float)
print("mean T =",a[:,0].mean()," mean |S|F_emp/logP =",a[:,1].mean()," mean |S|F_mod/logP =",a[:,2].mean())
print("mean F_emp =",a[:,3].mean()," mean F_mod =",a[:,4].mean())
m3=a[:,5]==1
print("N divisible by 3: mean T/(|S|/logP) =",(a[m3,0]/(a[m3,1]/a[m3,3])).mean(), " F_mod =",a[m3,4].mean())
print("N not div by 3:   mean T/(|S|/logP) =",(a[~m3,0]/(a[~m3,1]/a[~m3,3])).mean(), " F_mod =",a[~m3,4].mean())
print("c_2, c_3 model:", rho(K-math.log(2)/math.log(P))/rho(K), rho(K-math.log(3)/math.log(P))/rho(K))
