#!/usr/bin/env python3
"""Numerical companions to docs/residual-region.md, sections 7.5-7.12.

1. M(N) = sum_{l in I} log gcd(N - l, lcm(1..P)) over ALL even N in [P^{5/3}, P^2)
   (P = 1009) and over a random sample (P = 4001, 10007): max of M(N)/P and of
   M(N)/(K P), K = log N / log P.  Theorem A says a restricted-support family needs
   M(N) >= (K - o(1)) P.
2. log D_P / P, where D_P = lcm_i prod_{j != i} |l_i - l_j| (divided-difference route, 7.9).
3. Number of even N in (2P, P^2) with restricted support (BadFamily), compared with the
   large-sieve bound of Theorem LS (7.10).
4. Top range (P/2, P]: the geometric bound (7.12) vs the true sum; middle range (sqrt P, P/2]
   vs the lower bound (K - 0.847) P of Corollary G.

Usage: python3 scripts/residual_numerics.py
"""
import math
import random

import numpy as np


def primes_upto(n):
    s = np.ones(n + 1, dtype=bool)
    s[:2] = False
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]:
            s[i * i :: i] = False
    return np.nonzero(s)[0]


def prime_powers_upto(P, ps):
    out = []  # (d, log q)
    for q in ps:
        q = int(q)
        if q > P:
            break
        d = q
        while d <= P:
            out.append((d, math.log(q)))
            d *= q
    return out


def M_values(P, Ns, ps):
    I = [int(l) for l in ps if 3 <= l <= P]
    M = np.zeros(len(Ns))
    for d, lq in prime_powers_upto(P, ps):
        if d % 2 == 0:
            continue  # N - l is odd
        cnt = np.zeros(d, dtype=np.int64)
        for l in I:
            cnt[l % d] += 1
        M += lq * cnt[Ns % d]
    return M


def part1():
    print("== 1. M(N)/P over even N in [P^{5/3}, P^2) ==")
    for P, mode in ((1009, "all"), (4001, "sample"), (10007, "sample")):
        ps = primes_upto(P)
        lo, hi = int(P ** (5 / 3)), P * P
        if mode == "all":
            Ns = np.arange(lo + (lo % 2), hi, 2, dtype=np.int64)
        else:
            rng = np.random.default_rng(1)
            Ns = 2 * rng.integers(lo // 2, hi // 2, size=400_000, dtype=np.int64)
        M = M_values(P, Ns, ps)
        K = np.log(Ns.astype(float)) / math.log(P)
        r = M / P
        i = int(np.argmax(r))
        j = int(np.argmax(M / (K * P)))
        print(f"P={P} ({mode}, {len(Ns)} values): mean M/P={r.mean():.3f}, "
              f"max M/P={r.max():.3f} at N={Ns[i]} (K={K[i]:.3f}); "
              f"max M/(KP)={M[j] / (K[j] * P):.3f}")


def part2():
    print("== 2. log D_P / P (divided differences) ==")
    for P in (1009, 4001, 10007):
        ps = primes_upto(P)
        I = [int(l) for l in ps if 3 <= l <= P]
        logD = 0.0
        for q in ps:
            q = int(q)
            # v_q(D_P) = max_i sum_{a>=1} (#{j : l_j = l_i mod q^a} - 1)
            best = 0
            tot = {l: 0 for l in I}
            d = q
            while d <= P:
                cls = {}
                for l in I:
                    cls[l % d] = cls.get(l % d, 0) + 1
                for l in I:
                    tot[l] += cls[l % d] - 1
                d *= q
            best = max(tot.values())
            logD += best * math.log(q)
        print(f"P={P}: log D_P / P = {logD / P:.3f}")


def part3(Pmax=400):
    print("== 3. restricted-support even N in (2P, P^2) ==")
    lim = Pmax * Pmax
    gpf = np.zeros(lim + 1, dtype=np.int64)
    for q in primes_upto(lim):
        gpf[q::q] = q
    total = 0
    worst = (0, None)
    for P in range(11, Pmax + 1):
        ps = primes_upto(P)
        I = np.array([l for l in ps if l >= 3], dtype=np.int64)
        Ns = np.arange(2 * P + 2, P * P, 2, dtype=np.int64)
        ok = np.ones(len(Ns), dtype=bool)
        for l in I:
            ok &= gpf[Ns - l] < P
        c = int(ok.sum())
        total += c
        L = math.log(P)
        ratio = c / (P * L * L)
        if c and ratio > worst[0]:
            worst = (ratio, (P, c, Ns[ok][:5].tolist()))
    print(f"P in [11,{Pmax}]: total restricted-support N = {total}; "
          f"max count/(P log^2 P) = {worst[0]:.4f} at {worst[1]}")


def part4():
    """Top range (P/2, P]: geometric bound vs truth; middle range (sqrt P, P/2] vs K - 0.847."""
    print("== 4. top range (P/2,P] and middle range (sqrt P, P/2] ==")
    for P in (4001, 10007):
        ps = primes_upto(P)
        I = [int(l) for l in ps if 3 <= l <= P]
        rng = np.random.default_rng(2)
        lo, hi = int(P ** (5 / 3)), int(P ** 1.98)
        Ns = 2 * rng.integers(lo // 2, hi // 2, size=100_000, dtype=np.int64)
        K = np.log(Ns.astype(float)) / math.log(P)
        geo = np.zeros(len(Ns))
        top = np.zeros(len(Ns))
        mid = np.zeros(len(Ns))
        for q in ps:
            q = int(q)
            if q * q <= P or q < 3:
                continue
            lq = math.log(q)
            cnt = np.zeros(q, dtype=np.int64)
            for l in I:
                cnt[l % q] += 1
            n = cnt[Ns % q]
            if 2 * q > P:
                b0 = -((-(Ns - P)) // q)          # ceil((N-P)/q)
                b1 = (Ns - 3) // q                # floor((N-3)/q)
                b0 = b0 + (b0 % 2 == 0)           # first odd b >= b0
                geo += lq * (b0 <= b1)
                top += lq * n
            else:
                mid += lq * n
        print(f"P={P}: geometric top bound mean={geo.mean() / P:.4f} max={geo.max() / P:.4f} "
              f"(log2/2 = {math.log(2) / 2:.4f}); true top sum mean={top.mean() / P:.4f} "
              f"max={top.max() / P:.4f}")
        r = mid / ((K - 0.847) * P)
        print(f"        middle sum mean={mid.mean() / P:.3f}, max={mid.max() / P:.3f}; "
              f"max of middle/((K-0.847)P) = {r.max():.3f}")


if __name__ == "__main__":
    part1()
    part2()
    part3()
    part4()
