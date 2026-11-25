#!/usr/bin/env python3
"""Numerics for docs/switched-sieve.md.

1. Thresholds theta(K): least level theta with  theta + 8[1/(1+theta-K) - 1/(2-K)] < K.
2. Sanity check of Theorem S: sum_{P^theta0 < q <= P} log q * n_N(q)  vs  8P[1/(1+theta0-K) - 1/(2-K)].
3. The constant 4 log(3/2) of the "square-root cancellation" profile 1 - theta/2.
"""
import math
import numpy as np
from scipy.optimize import brentq

def G(theta, K):
    return 8 * (1 / (1 + theta - K) - 1 / (2 - K))

print("== 1. EH level needed ==")
for K in (5 / 3, 1.75, 1.8, 1.9, 1.95):
    f = lambda t: t + G(t, K) - K
    t = brentq(f, K - 1 + 1e-9, 1 - 1e-12)
    print(f"K={K:.3f}: theta > {t:.5f}   (1-theta < {1 - t:.5f}; (2-K)^2/13 = {(2 - K) ** 2 / 13:.5f})")

print("== 2. Theorem S, numerical sanity ==")
def primes(n):
    s = np.ones(n + 1, dtype=bool); s[:2] = False
    for i in range(2, int(n ** .5) + 1):
        if s[i]: s[i * i::i] = False
    return np.nonzero(s)[0]
for P in (4001, 20011):
    ps = primes(P); I = ps[ps >= 3]
    rng = np.random.default_rng(3)
    for K, th in ((1.7, 0.9), (1.7, 0.8), (1.9, 0.95)):
        worst = 0.0
        for _ in range(300):
            N = 2 * int(rng.integers(int(P ** K) // 2, int(P ** K * 1.01) // 2))
            tot = 0.0
            for q in ps[ps > P ** th]:
                q = int(q)
                tot += math.log(q) * int(np.count_nonzero((N - I) % q == 0))
            worst = max(worst, tot / P)
        print(f"P={P} K={K} theta0={th}: max over 300 N of sum/P = {worst:.4f}; "
              f"expected ~ {1 - th:.3f}; Theorem S bound = {G(th, K):.3f}")

print("== 3. square-root profile ==")
print("2*int_{1/2}^1 dtheta/(1-theta/2) = 4 log(3/2) =", 4 * math.log(1.5))
