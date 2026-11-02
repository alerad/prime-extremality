#!/usr/bin/env python3
"""Probe (floating point): thresholds k* = sup{k : int_0^y k u^{k-1} W(u) D(u) du >= 0 for all y}
for the configurations that block the weight-free method.
 (a) step at 3, T={2,3}, guaranteed weight W=(1-u^5)(1-u^7), D=(1-u^6)(1-u^9)-(1-u^3)
 (b) merged {2,3}-step, S={4,6,9}, W=(1-u^5)(1-u^7), D=P_S-(1-u^2)(1-u^3)  (y=1 gives k_9)
 (c) step at 5, T={2,3,5}, W=prod_{7<=q<=25}(1-u^q), D=(1-u^10)(1-u^15)(1-u^25)-(1-u^5)"""
import numpy as np
from sympy import primerange
u = np.linspace(0, 1, 400001)[1:]; du = u[1]-u[0]
def P(exps):
    out = np.ones_like(u)
    for e in exps: out *= 1 - u**e
    return out
def thr(W, D):
    ok = lambda k: (np.cumsum(k*u**(k-1)*W*D)*du).min() >= -1e-13
    lo, hi = 1.0, 2000.0
    if ok(hi): return np.inf
    for _ in range(60):
        mid = (lo+hi)/2
        lo, hi = (mid, hi) if ok(mid) else (lo, mid)
    return lo
W57 = P([5, 7])
print("(a) step at 3, T={2,3}:", round(thr(W57, P([6, 9]) - (1-u**3)), 3))
print("(b) merged S={4,6,9}  :", round(thr(W57, P([4, 6, 9]) - P([2, 3])), 3), "(k_9 = 125.840)")
W7_25 = P(list(primerange(7, 26)))
print("(c) step at 5, T={2,3,5}:", round(thr(W7_25, P([10, 15, 25]) - (1-u**5)), 3))
print("J-split at 7 without weights needs k <= 7*alpha_0 =", round(7*2.14312191825, 3))
