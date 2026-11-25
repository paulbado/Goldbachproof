#!/usr/bin/env python3
"""Low-height Wall II: are the constraints on the deficient rows alone contradictory?  (No.)

For a prime rank P (previous prime p) and even N with P^{5/3} <= N <= P^2 satisfying
PreviousRankConditions (N >= 3p+3, N = j mod p for a prime 3 <= j <= p), call a row i
(prime, 3 <= i <= P) *certificate-deficient* if every prime power r^a exactly dividing N - i
divides i - j for some prime j != i, 3 <= j <= P.  This is `DifferenceCertificate P i (N - i)`
of Goldbach/WilliamsonMurII.lean, i.e. everything that `Deficient` implies about the row itself.

The script counts the N in the band having >= 2 (>= 3) such rows, reports the maximum number of
such rows, and prints explicit witnesses.  These N are NOT bad families (some other row has a
prime factor >= P or is prime); the point is that the hypotheses "two deficient rows +
PreviousRankConditions" are satisfiable throughout the band, so no contradiction can come
from them alone.

Usage: python3 scripts/wall_ii_low_height_pairs.py [P ...]
"""
import sys
from math import log

def primes(n):
    s = bytearray([1]) * (n + 1); s[0] = s[1] = 0
    for i in range(2, int(n ** .5) + 1):
        if s[i]: s[i * i::i] = bytearray(len(s[i * i::i]))
    return [i for i in range(n + 1) if s[i]]

def factor(n, ps):
    out = []
    for r in ps:
        if r * r > n: break
        if n % r == 0:
            t = 1
            while n % r == 0: n //= r; t *= r
            out.append((r, t))
    if n > 1: out.append((n, n))
    return out

def run(P):
    ps = primes(P)
    I = [q for q in ps if q >= 3]
    p = I[-2]
    res = {j % p for j in I[:-1]}
    lo, hi = int(P ** (5 / 3)) + 1, P * P
    # shared[i] = set of prime powers t (odd) dividing some i - j, j != i prime index
    gaps = {i: {abs(i - j) for j in I if j != i} for i in I}
    def cert(i, m):
        for r, t in factor(m, ps):
            if r >= P or not any(g % t == 0 for g in gaps[i]): return False
        return True
    n2 = n3 = tot = 0; best = (0, None); first = None
    for N in range(lo + (lo % 2), hi + 1, 2):
        if N < 3 * p + 3 or N % p not in res: continue
        tot += 1
        rows = [i for i in I if cert(i, N - i)]
        if len(rows) >= 2:
            n2 += 1
            if first is None: first = (N, rows[:2])
        if len(rows) >= 3: n3 += 1
        if len(rows) > best[0]: best = (len(rows), N)
    bad = 0
    print(f"P={P} p={p}: {tot} admissible even N in [P^(5/3), P^2]; "
          f">=2 certificate rows: {n2}; >=3: {n3}; max rows: {best[0]} at N={best[1]} "
          f"(K={log(best[1]) / log(P):.3f})")
    N, (i, j) = first
    print(f"   witness: N={N} (K={log(N) / log(P):.3f}), rows i={i}, j={j}: "
          f"N-i={N - i}={factor(N - i, ps)}, N-j={N - j}={factor(N - j, ps)}")

if __name__ == "__main__":
    for P in ([int(a) for a in sys.argv[1:]] or [101, 199, 499]):
        run(P)
