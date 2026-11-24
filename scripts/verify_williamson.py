from math import isqrt

def primes(n):
    a=bytearray(b'\x01')*(n+1); a[:2]=b'\x00\x00'
    for p in range(2,isqrt(n)+1):
        if a[p]: a[p*p::p]=b'\x00'*((n-p*p)//p+1)
    return [p for p in range(2,n+1) if a[p]]
ps=primes(13*151)
I=[p for p in ps if 3<=p<=151]
total=0; worst=(0,None); hist=[]
for k,P in enumerate(I[1:],1):
    p=I[k-1]; indices=I[:k+1]; prev=set(j%p for j in indices[:-1]); qs=[q for q in ps if P<=q<=13*P]; count=0; local=0; survivor=[]
    for ell in indices:
        ds=[1]; diffs=[abs(j-ell) for j in indices if j!=ell]
        for r in indices:
            if r>(P-3)//2: break
            powers=[1]; t=r
            while t< P and any(v%t==0 for v in diffs): powers.append(t);t*=r
            ds=[d*t for d in ds for t in powers]
        forb=[(q,{(j-ell)%q for j in indices if j!=ell}) for q in qs]
        for d in ds:
            N=ell+d
            if N<3*p+3 or N%p not in prev: continue
            count+=1
            q=next((q for q,s in forb if d%q in s),None)
            if q is None: survivor.append((ell,d));continue
            if q/P>worst[0]: worst=(q/P,(P,ell,d,q))
            local=max(local,q)
    total+=count; hist.append((P,count,local,len(survivor)))
print('total',total,'worst',worst,'rows',hist)
assert total == 229153
assert all(row[3] == 0 for row in hist)
