#!/usr/bin/env python3
"""docs/localized-buchstab-wall-ii.tex, Section 5: idealised Chen/Buchstab balance for the localized problem l <= P (Buchstab-function model)."""
import numpy as np, math
from scipy.integrate import quad
h=1e-4; U=np.arange(1,40+h,h); w=np.zeros_like(U)
for k,u in enumerate(U):
    if u<=2: w[k]=1/u
    else:
        j=k-int(round(1/h)); w[k]=(U[k-1]*w[k-1]+h*w[j])/u
W=lambda v: float(np.interp(v,U,w))
g=math.exp(0.5772156649)
def fs(s): return 2*g*math.log(s-1)/s if 2<=s<=4 else None
print(" K     s   bad_tot  two-factor  ideal_upper  (lower<=1; f(s) if s<=4)")
for K in (5/3,1.75,1.8,1.9,1.95,1.99):
  for s in (2.5,3,4,6,10):
    beta=1/(2*s); u=K/beta
    # bad fraction among z-rough: 1 - good, good = rows with a prime factor >= P
    good=quad(lambda t: W(u*(1-t))/t, 1/K, 1-1/u, limit=200)[0]+1/u
    good/=W(u); bad=1-good
    norm=u*W(u)
    lo,hi=(K-1)/K,0.5
    b2=quad(lambda r:1/(r*(1-r)),lo,hi)[0]/norm
    up2=quad(lambda r:(2/(1-K*r))/(r*(1-r)),lo,hi)[0]/norm
    ideal=2*(bad-b2)+up2
    f=fs(s)
    print(f"{K:.3f} {s:4.1f}  {bad:.3f}   {b2:.4f}     {ideal:.3f}   {'' if f is None else f'f={f:.3f}'}")
