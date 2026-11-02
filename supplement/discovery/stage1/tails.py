#!/usr/bin/env python3
"""Refined tail envelopes (floating point exploration).
Blocks with max >= m_cut: split T = T_small (elements < B) u T_large (>= B). T_small lies in a
maximal antichain M of X cap [lo, B); P_T >= P_M * prod_{n in X, n >= B}(1 - v^n).
Weight: primes guaranteed by max T >= m_cut. Reports min over M of the threshold."""
import json, sys
import numpy as np
from sympy import primerange
sys.argv = [sys.argv[0]]
exec(open("explore.py").read().split("report = {}")[0])    # reuse helpers (no side effects)

def all_maximal_antichains(Xf):
    """maximal antichains of the finite sorted list Xf"""
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

def tail_threshold(X, lo, B, weight_primes, v, target):
    Ms = all_maximal_antichains([x for x in X if lo <= x < B])
    big = prod_one_minus([x for x in X if x >= B][:400], v)
    W = prod_one_minus(weight_primes, u)
    res = sorted((threshold(W * (prod_one_minus(M, v) * big - target)), M) for M in Ms)
    return len(Ms), res[:3]

X23 = smooth([2, 3], 4, 10**7)
P23 = (1 - u**2) * (1 - u**3)
for B, m0 in ((60, 200), (120, 200), (200, 400)):
    n, r = tail_threshold(X23, 4, B, list(primerange(5, m0 + 1)), u, P23)
    print(f"merged {{2,3}} tail: B={B}, weight primes [5,{m0}], {n} small parts: min k* = {r[0][0]:.2f} at {r[0][1]}", flush=True)
for p, mcut, Bs in ((5, 120, (40, 60, 90)), (7, 60, (30, 45))):
    Xp = smooth(list(primerange(2, p + 1)), 2, 10**7)
    for B in Bs:
        n, r = tail_threshold(Xp, 2, B, list(primerange(p + 1, p * mcut + 1)), u**p, 1 - u**p)
        print(f"p={p} tail: B={B}, weight primes ({p},{p*mcut}], {n} small parts: min k* = {r[0][0]:.2f} at {r[0][1]}", flush=True)
