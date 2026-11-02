#!/usr/bin/env python3
"""Stage 3 exploration (floating point): can the descent reach k_9 = 125.84?
 (i)  merged {2,3,5,7}: A = (primes in [11,N]) u S, S a 7-smooth antichain covering {2,3,5,7};
      weight prod_{11<=q<=max S}(1-u^q); integrand P_S - P_{2,3,5,7}.  Explicit S with max < MCUT,
      tail via small-part enumeration (B) with weight primes [11, MCUT].
 (ii) weighted single steps at 11 <= p <= 59 (explicit blocks with max T < m_p, refined tails).
"""
import json, sys, time
import numpy as np
from sympy import primerange

def progress(done, total=None, **f):
    print("ANVIL_PROGRESS " + json.dumps({"done": done, "total": total, **f}), flush=True)

u = np.linspace(0, 1, 200001)[1:]
du = u[1] - u[0]
KCAP = 300.0

def prod_one_minus(exps, x):
    out = np.ones_like(x)
    for e in exps:
        out *= 1 - x**e
    return out

def threshold(g):
    def ok(k):
        r = np.cumsum(k * u**(k - 1) * g) * du
        return r.min() >= -1e-9 * np.abs(r).max()
    if ok(KCAP):
        return KCAP
    if not ok(1.0):
        return 1.0
    lo, hi = 1.0, KCAP
    for _ in range(34):
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

def all_maximal_antichains(Xf):
    res = []
    def rec(i, chosen):
        if i == len(Xf):
            for x in Xf:
                if x not in chosen and not any(x % a == 0 or a % x == 0 for a in chosen):
                    return
            res.append(tuple(chosen)); return
        x = Xf[i]
        if not any(x % a == 0 for a in chosen):
            rec(i + 1, chosen + [x])
        rec(i + 1, chosen)
    rec(0, [])
    return res

R = (2, 3, 5, 7)
MCUT = int(sys.argv[1]) if len(sys.argv) > 1 else 64
X7 = smooth(R, 2, 10**7)
PR = prod_one_minus(R, u)
res = []
cands = [m for m in X7 if m < MCUT]
t0 = time.time()
progress(0, len(cands), phase="merged2357", unit="max element")
for i, m in enumerate(cands):
    W = prod_one_minus(list(primerange(11, m + 1)), u)
    for S in maximal_antichains_with_max(X7, m):
        if not all(any(s % r == 0 for s in S) for r in R):
            continue
        res.append((threshold(W * (prod_one_minus(S, u) - PR)), S))
    progress(i + 1, len(cands), phase="merged2357", unit="max element")
res.sort()
print(f"merged {{2,3,5,7}}: {len(res)} explicit S with max < {MCUT} ({time.time()-t0:.0f}s); smallest:", flush=True)
for t, S in res[:8]:
    print(f"   k* = {t:7.2f}  S = {S}", flush=True)
json.dump([(float(t), list(S)) for t, S in res[:200]], open(f"merged2357_explicit_{MCUT}.json", "w"))
for B in (24, 36):
    Ms = all_maximal_antichains([x for x in X7 if x < B])
    big = prod_one_minus([x for x in X7 if x >= B][:600], u)
    W = prod_one_minus(list(primerange(11, MCUT + 1)), u)
    tl = sorted((threshold(W * (prod_one_minus(M, u) * big - PR)), M) for M in Ms)
    print(f"   tail: B={B}, weight primes [11,{MCUT}], {len(Ms)} small parts: min k* = {tl[0][0]:.2f} at {tl[0][1]}", flush=True)

for p, mp, B in ((11, 30, 24), (13, 24, 20), (17, 20, 16), (19, 16, 14), (23, 14, 12), (29, 12, 10),
                 (31, 10, 9), (37, 9, 8), (41, 8, 7), (43, 8, 7), (47, 6, 6), (53, 6, 6), (59, 5, 5)):
    Xp = smooth(list(primerange(2, p + 1)), 2, 10**7)
    vp = u**p
    out = []
    for m in [x for x in Xp if x < mp]:
        W = prod_one_minus(list(primerange(p + 1, p * m + 1)), u)
        for T in maximal_antichains_with_max(Xp, m):
            out.append((threshold(W * (prod_one_minus(T, vp) - (1 - vp))), T))
    out.sort()
    Ms = all_maximal_antichains([x for x in Xp if x < B])
    big = prod_one_minus([x for x in Xp if x >= B][:600], vp)
    W = prod_one_minus(list(primerange(p + 1, p * mp + 1)), u)
    tl = sorted((threshold(W * (prod_one_minus(M, vp) * big - (1 - vp))), M) for M in Ms)
    print(f"p={p}: {len(out)} explicit (max<{mp}): min {out[0][0]:.2f} at {out[0][1]};  "
          f"tail B={B} ({len(Ms)} small parts): min {tl[0][0]:.2f} at {tl[0][1]}", flush=True)
