#!/usr/bin/env python3
"""Envelopes for compressing at 5 when every composite is {2,3,5}-smooth.
T is an antichain in <2,3,5>\{1}; R0 = T cap {2,3,5}. Envelope:
  E_R0(v) = prod_{r in R0}(1-v^r) * prod_{n in <2,3,5>, n>=4, no r in R0 divides n, n not in {2,3,5}} (1-v^n)
(the pointwise infimum of P_T over all T with T cap {2,3,5} = R0). Threshold s*(E)."""
import itertools, numpy as np
from scipy.optimize import brentq
LIM = 10**6
sm = sorted({2**a*3**b*5**c for a in range(25) for b in range(16) for c in range(10)
             if 2**a*3**b*5**c <= LIM} - {1})
v = np.linspace(0, 1, 300001)[1:-1]; dv = v[1]-v[0]
def env(R0):
    E = np.ones_like(v)
    for r in R0: E *= 1 - v**r
    for n in sm:
        if n in (2, 3, 5): continue
        if any(n % r == 0 for r in R0): continue
        E *= 1 - v**n
    return E
def thr(E):
    f = lambda s: (np.cumsum(v**(s-1)*(E-(1-v)))*dv)[-1]
    s0 = brentq(f, 0.5, 80)
    rmin = (np.cumsum(v**(s0-0.01-1)*(E-(1-v)))*dv).min()
    return s0, rmin
for k in range(4):
    for R0 in itertools.combinations((2, 3, 5), k):
        s0, rmin = thr(env(R0))
        print(f"R0={str(R0):10s} threshold s*={s0:8.4f}  -> k <= 5 s* = {5*s0:7.3f}   (runmin below: {rmin:.1e})")
print("7*alpha0 =", 7*2.14312191825192, "  3*(1+2sqrt3) =", 3*(1+2*np.sqrt(3)))
