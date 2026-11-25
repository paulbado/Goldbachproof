#!/usr/bin/env python3
"""docs/switched-sieve.md §5: Buchstab-function estimate of the Chen-type route (fraction of z-rough rows that are P-smooth, and the upper-bound loss allowed)."""
import numpy as np, math
# Buchstab omega on [1, 20] by delay ODE: (u w(u))' = w(u-1), w=1/u on [1,2]
h=1e-4; U=np.arange(1,20+h,h); w=np.zeros_like(U)
for k,u in enumerate(U):
    if u<=2: w[k]=1/u
    else:
        j=k-int(round(1/h)); w[k]=(U[k-1]*w[k-1]+h*w[j])/u
W=lambda v: np.interp(v,U,w)
g=math.exp(0.5772156649)
for K in (5/3,1.8,1.95):
  for beta in (1/6,1/8,1/10):   # z = P^beta
    u=K/beta
    t=np.linspace(1/K,1-1/u,20001)            # p = n^t, p >= P means t >= 1/K
    good=np.trapezoid(W(u*(1-t))/t,t)+1/u     # 1/u term: n prime (m=1)
    good/=W(u)
    s=0.5/beta    # level D = P^{1/2}
    f = (2*g*math.log(s-1)/s) if 2<=s<=4 else float('nan')
    print(f"K={K:.3f} z=P^{beta:.3f}: e^g*omega(u)={g*W(u):.3f}; good fraction among z-rough={good:.3f}, bad={1-good:.3f}; s={s:.1f}, f(s)={f:.3f}; needed upper-bound loss for bad < {(f/(g*W(u)))/(1-good) if f==f else float('nan'):.3f}")
