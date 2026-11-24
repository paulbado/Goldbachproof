#!/usr/bin/env python3
# Usage: python scripts/check_small_ranks.py B C
# Checks, for every prime rank 5 <= P <= B, that no bad family has a deficient
# line (hence no bad family at all, since one deficient line always exists):
# each candidate N = i + d (d built from prime powers t with 2t <= P-3 that
# divide some gap, cf. deficient_prime_power_bound) satisfying the previous-rank
# conditions is killed by a prime q in [P, C*P] dividing some N - j.
# Results: B=199 -> 2,960,556 candidates; B=271 -> 65,054,447; 0 survivors;
# max q/P = 12.55.
# Exhaustive check (archived method): for 5<=P<=B, every admissible
# deficient-line candidate N=i+d is killed by a prime q in [P, C*P] dividing some N-j.
import sys, time
from math import isqrt
B=int(sys.argv[1]); C=int(sys.argv[2])
def primes(n):
    a=bytearray(b'\x01')*(n+1); a[:2]=b'\x00\x00'
    for p in range(2,isqrt(n)+1):
        if a[p]: a[p*p::p]=b'\x00'*((n-p*p)//p+1)
    return [p for p in range(2,n+1) if a[p]]
ps=primes(C*B); I=[p for p in ps if 3<=p<=B]
total=0; t0=time.time(); worstratio=0
for k,P in enumerate(I[1:],1):
    p=I[k-1]; idx=I[:k+1]; prev={j%p for j in idx[:-1]}
    qs=[q for q in ps if P<=q<=C*P]; cnt=0; surv=0
    for ell in idx:
        ds=[1]; diffs=[abs(j-ell) for j in idx if j!=ell]
        for r in idx:
            if 2*r>P-3: break
            pw=[1]; t=r
            while 2*t<=P-3 and any(v%t==0 for v in diffs): pw.append(t); t*=r
            ds=[d*t for d in ds for t in pw]
        forb=[(q,{(j-ell)%q for j in idx if j!=ell}) for q in qs]
        for d in ds:
            N=ell+d
            if N<3*p+3 or N%2 or N%p not in prev: continue
            cnt+=1
            q=next((q for q,s in forb if d%q in s),None)
            if q is None: surv+=1; print("SURVIVOR",P,ell,d,flush=True)
            else: worstratio=max(worstratio,q/P)
    total+=cnt
    print(P,cnt,surv,f"{time.time()-t0:.0f}s",flush=True)
print("total",total,"max q/P",worstratio)
