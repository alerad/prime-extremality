#!/usr/bin/env python3
"""How many explicit blocks have more than one sign change on (0,1)? (floating point scan)"""
import itertools, json
import numpy as np
from sympy import primerange
src = open("stage3_explore.py").read().split("R = (2, 3, 5, 7)")[0]
exec(src)
x = np.linspace(0, 1, 200001)[1:-1]
def changes(vals):
    s = np.sign(vals[np.abs(vals) > 1e-13 * np.abs(vals).max()])
    return int(np.sum(s[1:] != s[:-1])), (s[0] if len(s) else 0)
R = (2, 3, 5, 7)
X7 = smooth(R, 2, 10**7)
PR = np.ones_like(x)
for r in R: PR *= 1 - x**r
multi = []
n = 0
for m in [y for y in X7 if y < 64]:
    for S in maximal_antichains_with_max(X7, m):
        if not all(any(s % r == 0 for s in S) for r in R): continue
        n += 1
        PS = np.ones_like(x)
        for s in S: PS *= 1 - x**s
        c, first = changes(PS - PR)
        if c != 1 or first < 0:
            multi.append((c, int(first), S))
print(f"merged explicit: {n} sets, {len(multi)} not single (+ then -) crossing")
for c in multi[:15]: print("  ", c)
for p in (11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59):
    Xp = smooth(list(primerange(2, p + 1)), 2, 10**7)
    bad = []; tot = 0
    for m in [y for y in Xp if y < 30]:
        for T in maximal_antichains_with_max(Xp, m):
            tot += 1
            ET = np.ones_like(x)
            for t in T: ET *= 1 - x**t
            c, first = changes(ET - (1 - x))
            if c != 1 or first < 0: bad.append((c, int(first), T))
    print(f"p={p}: {tot} blocks (max<30), {len(bad)} not single crossing", bad[:5])
