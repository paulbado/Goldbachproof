#!/usr/bin/env python3
"""docs/tex/localized-buchstab-wall-ii.tex, Sections 5-6: idealised localized balance U_ideal(K,s), its limit 2(1-log K),
and the true linear-sieve functions F(s), f(s) (delay-differential equations) for s > 4."""
import numpy as np, math
from scipy.integrate import quad
g=math.exp(0.5772156649015329)
# Buchstab omega on [1,250]
h=2e-4; U=np.arange(1,250+h,h); w=np.zeros_like(U); n1=int(round(1/h))
for k in range(len(U)):
    u=U[k]
    if u<=2: w[k]=1/u
    else: w[k]=(U[k-1]*w[k-1]+h*0.5*(w[k-n1]+w[k-1-n1]))/u
W=lambda v: float(np.interp(v,U,w))
# linear sieve F,f: F=2e^g/s (0<s<=3), f=0 (s<=2); (sF)'=f(s-1) s>3; (sf)'=F(s-1) s>2
H=1e-4; S=np.arange(0.5,80+H,H); F=np.zeros_like(S); f=np.zeros_like(S); m=int(round(1/H))
for k,s in enumerate(S):
    if s<=3: F[k]=2*g/s
    if s<=2: f[k]=0
    if k>0:
        if s>3: F[k]=(S[k-1]*F[k-1]+H*0.5*(f[k-m]+f[k-1-m]))/s
        if s>2: f[k]=(S[k-1]*f[k-1]+H*0.5*(F[k-m]+F[k-1-m]))/s
Ff=lambda s:(float(np.interp(s,S,F)),float(np.interp(s,S,f)))
print("check f(3),f(4):",Ff(3)[1],2*g*math.log(2)/3, Ff(4)[1], 2*g*math.log(3)/4)
def Uid(K,s):
    u=2*s*K; norm=u*W(u)
    good=(quad(lambda t: W(u*(1-t))/t,1/K,1-1/u,limit=400)[0]+1/u)/W(u)
    bad=1-good; lo=(K-1)/K
    b2=quad(lambda r:1/(r*(1-r)),lo,.5)[0]/norm
    up2=quad(lambda r:(2/(1-K*r))/(r*(1-r)),lo,.5)[0]/norm
    return 2*(bad-b2)+up2, bad, u
print(" K      s   U_ideal  limit 2(1-logK)  lower=f(s)/(e^g w(u))  F(s)/(e^g w(u))  margin(lower-U)")
for K in (5/3,1.7,1.75,1.8):
    for s in (4,6,10,20,40,60):
        Ui,bad,u=Uid(K,s); Fs,fs=Ff(s); nrm=g*W(u)
        print(f"{K:.3f} {s:4d}  {Ui:.4f}   {2*(1-math.log(K)):.5f}        {fs/nrm:.5f}            {Fs/nrm:.5f}      {fs/nrm-Ui:+.4f}")
