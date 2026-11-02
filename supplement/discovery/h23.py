#!/usr/bin/env python3
"""Thresholds for the {2,3}-smooth case analysis (exploration, floating point):
 (i)  T contains 2 or 3  =>  P_T >= (1-v^2)(1-v^3)
 (ii) T avoids 2,3       =>  P_T >= H23(v) = prod_{n in <2,3>, n>=4} (1-v^n)
For each envelope E, s*(E) = sup{s : int_0^z v^{s-1}(E(v)-(1-v)) dv >= 0 for all z}."""
import numpy as np
from scipy.optimize import brentq
sm = sorted({2**a*3**b for a in range(0, 60) for b in range(0, 40) if 2**a*3**b <= 10**7} - {1, 2, 3})
v = np.linspace(0, 1, 400001)[1:-1]; dv = v[1]-v[0]
H23 = np.ones_like(v)
for n in sm:
    H23 *= 1 - v**n
E1 = (1-v**2)*(1-v**3)
def runmin(E, s):
    r = np.cumsum(v**(s-1)*(E-(1-v)))*dv
    return r.min(), r[-1]
for name, E in (("(1-v^2)(1-v^3)", E1), ("H23 (no 2,3)", H23)):
    s0 = brentq(lambda s: runmin(E, s)[1], 1.0, 60)
    print(f"{name:18s} threshold s* = {s0:.6f};  run-min at s*-0.01: {runmin(E, s0-0.01)[0]:.3e}")
print("1+2*sqrt(3) =", 1+2*np.sqrt(3), "  5*alpha0/3 =", 5*2.14312191825192/3)
