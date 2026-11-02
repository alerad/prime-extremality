#!/usr/bin/env python3
"""Viability probe (floating point) for weight-aware compressions toward k_9 = 125.84.
Step at prime p with p-smooth block T: guaranteed weight = primes in (p, p*max T].
Threshold = sup{k : int_0^y k u^{k-1} W(u) [P_T(u^p) - (1-u^p)] du >= 0 for all y}."""
import numpy as np
from sympy import primerange
u = np.linspace(0, 1, 400001)[1:]; du = u[1]-u[0]
def P(exps, x):
    out = np.ones_like(x)
    for e in exps: out *= 1 - x**e
    return out
def thr(p, T):
    W = P(list(primerange(p+1, p*max(T)+1)), u)
    D = P(T, u**p) - (1 - u**p)
    def ok(k):
        r = np.cumsum(k*u**(k-1)*W*D)*du
        return r.min() >= -1e-9*np.abs(r).max()      # relative tolerance
    lo, hi = 1.0, 300.0
    if ok(hi): return float('inf')                    # reported as '>300'
    for _ in range(60):
        mid = (lo+hi)/2
        lo, hi = (mid, hi) if ok(mid) else (lo, mid)
    return lo
cases = {5: [[2, 3], [2, 3, 5], [4, 6, 9], [2, 9], [3, 4]],
         7: [[2, 3], [2, 3, 5], [2, 3, 5, 7], [4, 6, 9], [2, 5], [3, 5]],
         11: [[2, 3], [2, 3, 5, 7], [2, 3, 5, 7, 11]],
         13: [[2, 3], [2, 3, 5, 7, 11, 13]]}
for p, Ts in cases.items():
    print(f"p={p}: " + ";  ".join(f"T={T}: " + (">300" if thr(p, T) == float("inf") else f"{thr(p, T):.1f}") for T in Ts), flush=True)
