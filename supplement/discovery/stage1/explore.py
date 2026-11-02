#!/usr/bin/env python3
"""Stage 1 exploration (floating point, not a certificate).

Weighted ordered descent: process primes p >= 5 from large to small; at prime p every
composite is p-smooth and (after adding missing primes) A contains all primes in (p, N].
Compressing at p with block T (an antichain of p-smooth numbers) is admissible at exponent
k if the running integrals of  k u^(k-1) W(u) [P_T(u^p) - (1 - u^p)]  are >= 0, where
W = prod_{p < q <= p max T} (1 - u^q)  (guaranteed part of P_B).
Final merged {2,3} step: S antichain in <2,3> \ {1,2,3} containing an even element and a
multiple of 3; weight prod_{5 <= q <= max S}(1-u^q); integrand P_S(u) - (1-u^2)(1-u^3).
Reports the minimal thresholds over explicit blocks with max < m_cut, and tail checks.
"""
import json, sys, time
import numpy as np
from sympy import primerange

def progress(done, total=None, **f):
    print("ANVIL_PROGRESS " + json.dumps({"done": done, "total": total, **f}), flush=True)

GRID = 200001
u = np.linspace(0, 1, GRID)[1:]
du = u[1] - u[0]
KCAP = 200.0

def prod_one_minus(exps, x):
    out = np.ones_like(x)
    for e in exps:
        out *= 1 - x**e
    return out

def threshold(g):
    """sup{k in [1,KCAP] : cumsum(k u^(k-1) g) >= 0 everywhere} (relative tolerance)."""
    def ok(k):
        r = np.cumsum(k * u**(k - 1) * g) * du
        return r.min() >= -1e-9 * np.abs(r).max()
    if ok(KCAP):
        return KCAP
    if not ok(1.0):
        return 1.0
    lo, hi = 1.0, KCAP
    for _ in range(36):
        mid = (lo + hi) / 2
        lo, hi = (mid, hi) if ok(mid) else (lo, mid)
    return lo

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

def maximal_antichains_with_max(X, m):
    """All antichains of X (sorted) that contain m, lie in [.., m], and are maximal in X∩[2,m]."""
    Xm = [x for x in X if x <= m]
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

report = {}
# ---------- merged {2,3} ----------
X23 = smooth([2, 3], 4, 10**6)
M0 = int(sys.argv[1]) if len(sys.argv) > 1 else 200
best = []
cands = [m for m in X23 if m < M0]
progress(0, len(cands), phase="merged23", unit="max")
P23 = (1 - u**2) * (1 - u**3)
for i, m in enumerate(cands):
    for S in maximal_antichains_with_max(X23, m):
        if not any(s % 2 == 0 for s in S) or not any(s % 3 == 0 for s in S):
            continue
        W = prod_one_minus(list(primerange(5, m + 1)), u)
        t = threshold(W * (prod_one_minus(S, u) - P23))
        best.append((t, S))
    progress(i + 1, len(cands), phase="merged23", unit="max")
best.sort()
print("merged {2,3}: smallest thresholds over S with max S <", M0)
for t, S in best[:6]:
    print(f"   k* = {t:7.2f}  S = {S}")
H23 = prod_one_minus(X23[:200], u)
for m0 in (50, 100, 200, 400):
    W = prod_one_minus(list(primerange(5, m0 + 1)), u)
    print(f"   tail (H23 envelope, weight primes [5,{m0}]): k* = {threshold(W * (H23 - P23)):.2f}")
report["merged23"] = best[:20]

# ---------- weighted single steps ----------
cuts = {5: 120, 7: 60, 11: 30, 13: 30, 17: 24, 19: 24, 23: 24}
for p, mcut in cuts.items():
    Xp = smooth(list(primerange(2, p + 1)), 2, 10**6)
    out = []
    cands = [m for m in Xp if m < mcut]
    t0 = time.time()
    progress(0, len(cands), phase=f"p={p}", unit="max")
    vp = u**p
    for i, m in enumerate(cands):
        W = prod_one_minus(list(primerange(p + 1, p * m + 1)), u)
        for T in maximal_antichains_with_max(Xp, m):
            g = W * (prod_one_minus(T, vp) - (1 - vp))
            out.append((threshold(g), T))
        progress(i + 1, len(cands), phase=f"p={p}", unit="max")
    out.sort()
    print(f"p={p}: {len(out)} blocks with max T < {mcut} ({time.time()-t0:.0f}s); smallest thresholds:")
    for t, T in out[:5]:
        print(f"   k* = {t:7.2f}  T = {T}")
    Hp = prod_one_minus(Xp[:400], vp)
    for mt in sorted({mcut, 2 * mcut}):
        W = prod_one_minus(list(primerange(p + 1, p * mt + 1)), u)
        print(f"   tail (H_p envelope, weight primes ({p},{p*mt}]): k* = {threshold(W * (Hp - (1 - vp))):.2f}")
    report[f"p{p}"] = out[:20]
json.dump({k: [(float(t), list(map(int, S))) for t, S in v] for k, v in report.items()},
          open("explore_results.json", "w"), indent=1)
