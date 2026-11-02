#!/usr/bin/env python3
"""s_{23}: largest s with int_0^z v^{s-1}(P_T(v)-(1-v)) dv >= 0 for all z in (0,1], over all
maximal antichains (staircases) T in {2^a 3^b} minus {1}. Floating point exploration."""
import numpy as np
from scipy.optimize import brentq

BOUND = 3**8
def staircases():
    # maximal antichains in N^2\{0}: (a0,0)=...=(0,br) paths, steps with
    # (a_i - a_{i+1} - 1)(b_{i+1} - b_i - 1) = 0
    out = []
    def rec(path):
        a, b = path[-1]
        if a == 0:
            out.append(list(path)); return
        # next point (a2, b2): a2 < a, b2 > b
        for a2 in range(a-1, -1, -1):
            for b2 in range(b+1, 40):
                if (a - a2 - 1)*(b2 - b - 1) != 0: continue
                if 2**a2 * 3**b2 > BOUND: break
                rec(path + [(a2, b2)])
    for a0 in range(1, 40):
        if 2**a0 > BOUND: break
        rec([(a0, 0)])
    return [[2**a*3**b for a, b in p] for p in out]

v = np.linspace(1e-9, 1-1e-9, 200001)
dv = v[1]-v[0]
def worst(T, s):
    PT = np.ones_like(v)
    for t in T: PT *= 1 - v**t
    g = v**(s-1)*(PT - (1-v))
    run = np.cumsum(g)*dv
    return run.min(), run[-1]

Ts = staircases()
print(len(Ts), "staircases with elements <=", BOUND)
res = []
for T in Ts:
    f = lambda s: worst(T, s)[1]
    if f(30) >= 0:
        res.append((np.inf, T)); continue
    s0 = brentq(f, 1.0, 30)
    # check running minimum at slightly below s0 is not negative earlier
    m, _ = worst(T, s0 - 1e-3)
    res.append((s0, T, m))
res.sort(key=lambda r: r[0])
for r in res[:12]:
    print(round(r[0], 5), r[1], "" if len(r) < 3 else f"runmin just below: {r[2]:.2e}")
