#!/usr/bin/env python3
"""Moment certificate for Lemma (weighted crossing) / Proposition (powers x^k).

Exact part (pure Python, Fractions): with R(x) = prod_{p in {3,5,7,11,13,17}} (1 - x^p),
    J_{17/8}(1) >= int_0^1 x^{9/8} R(x)(1 - x^2 - x^19) dx - 64/425 > 1/20000,
using int_0^1 x^{9/8+m} dx = 8/(8m+17); and
    J_3(1) <= int_0^1 x^2 ((1-x^2)(1-x^3)(1-x^5) - (1-x)) dx = -23/8580.

Floating-point part (requires numpy; skipped otherwise): alpha_0 = sup{b : J_b(1) > 0},
the root of int_0^1 x^{b-1} Q(x) dx = 1/(b(b+1)), Q(x) = prod_p (1 - x^p).
Exits with nonzero status if an exact check fails.
"""
import sys
from fractions import Fraction as F


def polymul(a, b):
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                r[i + j] += x * y
    return r


def one_minus(p):
    q = [0] * (p + 1)
    q[0], q[p] = 1, -1
    return q


R = [1]
for p in [3, 5, 7, 11, 13, 17]:
    R = polymul(R, one_minus(p))
poly = polymul(R, [1, 0, -1] + [0] * 16 + [-1])  # times (1 - x^2 - x^19)
assert len(poly) - 1 == 75

lhs = sum(F(8 * c, 8 * m + 17) for m, c in enumerate(poly) if c) - F(64, 425)
print("J_{17/8}(1) lower bound =", float(lhs))
print("  exact:", lhs)
ok1 = lhs > F(1, 20000)
print("  > 1/20000:", ok1)

P = polymul(polymul(one_minus(2), one_minus(3)), one_minus(5))
J3 = sum(F(c, m + 3) for m, c in enumerate(P) if c) - (F(1, 3) - F(1, 4))
ok2 = J3 == F(-23, 8580)
print("J_3(1) upper bound =", J3, "(= -23/8580:", ok2, ")")

try:
    import numpy as np
except ImportError:
    print("numpy not available: skipping alpha_0")
else:
    N = 400000
    s = np.ones(N + 1, bool)
    s[:2] = False
    for i in range(2, int(N ** 0.5) + 1):
        if s[i]:
            s[i * i :: i] = False
    primes = np.nonzero(s)[0].astype(float)
    w = np.linspace(np.log(1e-7), np.log(60.0), 40000)
    t = np.exp(w)
    Phi = np.zeros_like(t)
    for chunk in np.array_split(primes, 200):
        Phi += -np.log1p(-np.exp(-np.outer(chunk, t))).sum(0)
    trap = getattr(np, "trapezoid", None) or np.trapz

    def J(b):  # int_0^1 x^{b-1}(Q - (1-x)) dx in the variable x = e^{-t}
        return trap(np.exp(-b * t - Phi) * t, w) - 1 / (b * (b + 1))

    lo, hi = 2.0, 3.0
    for _ in range(60):
        mid = (lo + hi) / 2
        lo, hi = (mid, hi) if J(mid) > 0 else (lo, mid)
    print(f"alpha_0 ~ {lo:.10f}, 2*alpha_0 ~ {2 * lo:.10f}  (floating point)")

sys.exit(0 if ok1 and ok2 else 1)
