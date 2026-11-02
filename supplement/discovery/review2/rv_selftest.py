#!/usr/bin/env python3
"""Self-tests of my root counter / running-integral decider against brute force."""
import random, flint
import numpy as np
from fractions import Fraction as Fr
from rv_common import *

def poly_from_roots(rts, extra=()):
    p = flint.fmpz_poly([1])
    for (a, b) in rts:            # root a/b
        p *= flint.fmpz_poly([-a, b])
    for q in extra:
        p *= flint.fmpz_poly(q)
    return p

tests = [
    (poly_from_roots([(1,3),(1,2),(2,3)]), 3),
    (poly_from_roots([(1,3),(1,3),(1,2)]), 2),
    (flint.fmpz_poly([1,0,1]), 0),
    (poly_from_roots([(9,10),(11,10)]), 1),
    (poly_from_roots([(500,1000),(500,1001)]), 2),
    (poly_from_roots([(500,1000),(500,1001),(500,999)],[[1,0,1]]), 3),
    (poly_from_roots([(1,1000000),(999999,1000000)]), 2),
    (poly_from_roots([(7,5),(-1,2)]), 0),
    (poly_from_roots([(1,2)]*5), 1),
    (poly_from_roots([(1,2)]*4 + [(1,3)]), 2),
]
for p, n in tests:
    got = count_roots_01(p)
    print("count", got, "expected", n, "OK" if got == n else "FAIL")

# random polynomials: compare distinct-root count with numpy roots (well separated cases only)
random.seed(5); bad = 0; tried = 0
for trial in range(400):
    deg = random.randint(1, 12)
    rts = []
    for _ in range(deg):
        b = random.randint(2, 40); a = random.randint(-b, 2*b)
        rts.append((a, b))
    p = poly_from_roots(rts, [[1, 0, 1]] if random.random() < .5 else [])
    exact = len({Fr(a, b) for a, b in rts if 0 < Fr(a, b) < 1})
    got = count_roots_01(p); tried += 1
    if got != exact:
        bad += 1; print("MISMATCH", rts, got, exact)
print(f"random root tests: {tried} tried, {bad} mismatches")

# sign pattern tests
print(sign_pattern(poly_from_roots([(1,2)], [[0,1],[1,-1],[1,-1]]) * flint.fmpz_poly([-1])), "(expect single+- : -(u)(1-u)^2(2u-1) )")
print(sign_pattern(poly_from_roots([(1,2),(1,2)], [[0,0,1]])), "(expect other: double root, + + )")
print(sign_pattern(poly_from_roots([(1,3),(1,2),(2,3)]) * flint.fmpz_poly([-1])), "(expect other: 3 roots)")

# running integral decider vs brute force on random polys with K=1..5
random.seed(7); bad = 0
ys = np.linspace(1e-4, 1, 200001)
for trial in range(300):
    deg = random.randint(1, 8)
    c = [random.randint(-30, 30) for _ in range(deg + 1)]
    c[0] = abs(c[0]) + 1 if random.random() < .8 else c[0]
    K = random.randint(1, 5)
    g = flint.fmpz_poly(c)
    ok, r1 = running_integral_positive(g, K)
    # brute force: r(y) = sum c_n K/(K+n) y^n, R = y^K r
    r = sum(c[n] * K / (K + n) * ys**n for n in range(len(c)))
    bf = bool(np.all(r > 0))
    if ok != bf:
        # near-tangency cases may disagree in floating point; report
        bad += 1; print("DISAGREE", c, K, ok, bf, r.min())
print(f"running-integral tests: 300 tried, {bad} disagreements")
