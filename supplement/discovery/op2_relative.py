#!/usr/bin/env python3
"""OP2 relative version: test family U = {D} u D*P (Min(U) = {D}).
For weight w(u) = k u^{k-1}:  int_0^1 w(u)[Q(u^D) - (1-u^D)] du = (k/D) J_{k/D}(1).
High-precision quadrature (mpmath), Q from primes up to PMAX (tail bound tiny for x<=1-...)."""
import mpmath as mp
from sympy import primerange
mp.mp.dps = 30
PR = list(primerange(2, 20000))

def logQ(x):
    # log prod_p (1 - x^p); for x close to 1 use t = -log x with enough primes
    s = mp.mpf(0)
    for p in PR:
        y = x**p
        if y < mp.mpf(10)**(-35): break
        s += mp.log1p(-y)
    return s

def Q(x):
    if x >= 1: return mp.mpf(0)
    return mp.e**logQ(x)

def J(s, z=1):
    f = lambda x: x**(s-1)*(Q(x)-(1-x))
    return mp.quad(f, [0, 0.3, 0.567, 0.8, 0.95, 0.99, z])

# alpha_0 = root of J_s(1) = 0
a0 = mp.findroot(lambda s: J(s), 2.14)
print("alpha_0 =", mp.nstr(a0, 15), " 2*alpha_0 =", mp.nstr(2*a0, 15))
for k in (4.25, 4.28, 4.29, 4.3, 5, 6):
    print(f"k={k}: relative test (D=2) value (k/2)J_(k/2)(1) = {mp.nstr(mp.mpf(k)/2*J(mp.mpf(k)/2), 8)}")
# E[-log Z_P] = int_0^1 (1-Q(x))/x dx  (D -> infinity behaviour)
print("E[-log Z_P] =", mp.nstr(mp.quad(lambda x: (1-Q(x))/x, [0, 0.3, 0.6, 0.9, 0.99, 1]), 12), "(compare E[-log U] = 1)")
