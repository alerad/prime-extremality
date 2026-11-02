#!/usr/bin/env python3
"""OP2 absolute version, exhaustive for small N: for every maximal primitive A in [2,N],
find where E Z_A^k - E Z_{P_N}^k changes sign for k in (0, KMAX]. 60-digit floats, then
bisection. Evidence only."""
import sys, json
import mpmath as mp
from sympy import primerange
mp.mp.dps = 80
KMAX = 400

def max_antichains(N):
    nums = list(range(2, N+1))
    res = []
    def rec(i, chosen):
        if i == len(nums):
            S = set(chosen)
            for n in nums:
                if n in S: continue
                if not any(n % a == 0 or a % n == 0 for a in chosen):
                    return
            res.append(tuple(chosen)); return
        n = nums[i]
        if not any(n % a == 0 for a in chosen):
            chosen.append(n); rec(i+1, chosen); chosen.pop()
        # exclude n: allowed only if it can still become comparable later or already is
        if any(n % a == 0 for a in chosen) or any(m % n == 0 for m in range(2*n, N+1, n)):
            rec(i+1, chosen)
    rec(0, [])
    return res

def poly(A):
    c = {0: 1}
    for a in A:
        d = dict(c)
        for j, v in c.items():
            d[j+a] = d.get(j+a, 0) - v
        c = {j: v for j, v in d.items() if v}
    return c

def moment(c, k):
    k = mp.mpf(k)
    return mp.fsum(v*k/(k+j) for j, v in c.items())

def scan(N):
    P = tuple(primerange(2, N+1))
    cP = poly(P)
    ants = max_antichains(N)
    grid = [mp.mpf(x)/4 for x in range(4, 4*KMAX+1)]   # k = 1, 1.25, ..., KMAX
    best = None
    for A in ants:
        if A == P: continue
        cA = poly(A)
        diff = {j: cA.get(j, 0) - cP.get(j, 0) for j in set(cA) | set(cP)}
        prev = moment(diff, grid[0])
        assert prev > 0, (A, prev)
        for k in grid[1:]:
            cur = moment(diff, k)
            if cur < 0:
                lo, hi = k - mp.mpf(1)/4, k
                for _ in range(40):
                    mid = (lo+hi)/2
                    if moment(diff, mid) < 0: hi = mid
                    else: lo = mid
                if best is None or hi < best[0]:
                    best = (hi, A)
                break
            prev = cur
    return len(ants), best

for N in range(4, int(sys.argv[1]) + 1 if len(sys.argv) > 1 else 31):
    n, best = scan(N)
    if best:
        print(f"N={N:3d} #maxantichains={n:7d} first crossing k={mp.nstr(best[0], 12)} by {best[1]}", flush=True)
    else:
        print(f"N={N:3d} #maxantichains={n:7d} primes win for all k<= {KMAX}", flush=True)
