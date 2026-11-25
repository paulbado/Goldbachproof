#!/usr/bin/env python3
"""Numerics for docs/distribution-profile.md: C(lambda) = 2*int_{1/2}^1 dtheta/lambda(theta) for the
available profile, a hypothetical large-sieve profile, and the minimal admissible profiles of each family."""
import numpy as np
from scipy.optimize import brentq
from scipy.integrate import quad
def C(lam): return 2*quad(lambda t:1/lam(t),0.5,1,limit=400,points=[0.8,0.99225,0.99])[0]
sig=lambda t:t/248
avail=lambda t:max(1-t,(31/47)*(1-t+sig(t)))
print("C(available 16.2chi/16.3chi profile) =",C(avail))
ls=lambda t:max(1-t,min(2*(1-t),t/2),(31/47)*(1-t+sig(t)))
print("C(hypothetical large-sieve profile) =",C(ls))
for K in (5/3,1.8,1.9,2.0):
    tgt=K-0.5
    f=lambda c: C(lambda t:min(1,1-t+c))-tgt
    c=brentq(f,1e-3,1.0)
    g=lambda b: C(lambda t:max(1-t,b))-tgt   # floor profile
    b=brentq(g,0.05,1.0)
    # threshold: trivial on [1/2,1-u], level 1 on [1-u,1]
    h=lambda u: 2*(np.log(1/(2*u))+u)-tgt
    u=brentq(h,0.01,0.5)
    print(f"K={K:.3f}: target {tgt:.3f}; uniform lambda>{2/(2*K-1):.3f}; additive gain c>{c:.3f}; floor b>{b:.3f}; level 1 needed on theta>{1-u:.3f}")
