#!/usr/bin/env python3
"""Counterexample search for the conjecture k* = k_9 = 125.84 (floating point, evidence only).

Every competitor can be taken as A = (P_N \\ R) u S with R a set of primes and S an antichain of
R-smooth composites covering R (every r in R divides some s in S); missing primes outside R are
addable. For each R and each S maximal in <R> \\cap [4, m] with m = max S, and N = m (lightest
weight) and N = 2m, evaluate f(k) = E Z_A^k - E Z_{P_N}^k at k = 120 and k = 125.8 with stable
Gauss-Laguerre quadrature (products evaluated directly). Any f < 0 is reported.
"""
import json, sys, time, itertools
import numpy as np
from sympy import primerange

def progress(done, total=None, **f):
    print("ANVIL_PROGRESS " + json.dumps({"done": done, "total": total, **f}), flush=True)

KS = np.array([120.0, 125.8])
uu, ww = np.polynomial.laguerre.laggauss(60)
X = np.exp(-np.outer(1.0 / KS, uu))            # (len(KS), nodes)
LX = np.log(X)

def logP(exps):
    s = np.zeros_like(X)
    for e in exps:
        s += np.log1p(-np.exp(e * LX))
    return s

def smooth(primes, lo, hi):
    out = {1}
    for p in primes:
        new = set()
        for x in out:
            y = x
            while y <= hi:
                new.add(y); y *= p
        out = new
    return sorted(n for n in out if lo <= n <= hi)

def maximal_antichains_with_max(Xs, m):
    Xm = [x for x in Xs if x <= m]
    res = []
    def rec(i, chosen):
        if i == len(Xm):
            if m not in chosen:
                return
            for x in Xm:
                if x not in chosen and not any(x % a == 0 or a % x == 0 for a in chosen):
                    return
            res.append(tuple(chosen)); return
        x = Xm[i]
        if x == m:
            if not any(x % a == 0 for a in chosen):
                rec(i + 1, chosen + [x])
            return
        if not any(x % a == 0 for a in chosen) and m % x != 0:
            rec(i + 1, chosen + [x])
        rec(i + 1, chosen)
    rec(0, [])
    return res

plan = [((2, 3), 3000), ((2, 5), 1500), ((3, 5), 1500), ((2, 7), 1000), ((2, 3, 5), 160),
        ((2, 3, 7), 140), ((2, 5, 7), 140), ((3, 5, 7), 140), ((2, 3, 5, 7), 72), ((2, 3, 11), 120),
        ((2, 3, 5, 7, 11), 50)]
worst = []
t0 = time.time()
for pi, (R, M) in enumerate(plan):
    comps = [n for n in smooth(R, 4, M) if n not in R]
    count = 0
    progress(0, len(comps), phase=f"R={R}", unit="max element")
    for i, m in enumerate(comps):
        for S in maximal_antichains_with_max(comps, m):
            if not all(any(s % r == 0 for s in S) for r in R):
                continue
            count += 1
            for N in (m, 2 * m):
                others = [q for q in primerange(2, N + 1) if q not in R]
                base = logP(others)
                f = (np.exp(base + logP(S)) - np.exp(base + logP(R))) @ ww
                worst.append((float(f[1] / (np.abs(f).max() + 1e-300)), R, S, N, f.tolist()))
                if f.min() < 0:
                    print(f"NEGATIVE: R={R} S={S} N={N} f(120,125.8)={f}", flush=True)
        progress(i + 1, len(comps), phase=f"R={R}", unit="max element")
    print(f"R={R}: {count} antichains S (max <= {M}) checked, {time.time()-t0:.0f}s elapsed", flush=True)
worst.sort(key=lambda r: r[0])
print("closest to failure (normalised f at k=125.8):")
for w in worst[:10]:
    print("  ", round(w[0], 4), "R=", w[1], "S=", w[2], "N=", w[3])
