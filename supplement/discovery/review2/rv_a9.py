#!/usr/bin/env python3
"""A_9 bracket and k_9, independently: exact rationals + mpmath root (from exact coefficients)."""
from fractions import Fraction as Fr
import mpmath as mp
from rv_common import P_poly, coeffs, sign_pattern, RK1_exact, running_integral_positive, RSET, A9
mp.mp.dps = 60
D = P_poly(A9) - P_poly(RSET)
c = coeffs(D)
print("D = P_A9 - P_2357 coefficients:", c)
print("sign pattern of D on (0,1):", sign_pattern(D))
for k in (Fr(12584, 100), Fr(12585, 100), Fr(125840454069445, 10**12), Fr(125840454069446, 10**12)):
    print(f"R_k(1) at k={float(k)!r}: {float(RK1_exact(D, k)):.6e}")
f = lambda k: mp.fsum(mp.mpf(cn) * k / (k + n) for n, cn in enumerate(c) if cn)
k9 = mp.findroot(f, 125.84)
print("k_9 =", mp.nstr(k9, 40))
print("claimed 125.84045406944565748; |diff| =", mp.nstr(abs(k9 - mp.mpf("125.84045406944565748")), 5))
# E Z^k difference for several k: sign must be + below k9, - above (single crossing in k)
for k in (1, 10, 50, 100, 125, 125.84, 125.85, 126, 150, 300):
    print(k, mp.nstr(f(mp.mpf(k)), 8))
# extra: S = {4,5,7,9} (dominated only by A_9 among maximal sets with max 9): check at K = 126 directly
for S in [(4, 5, 7, 9), (5, 6, 7, 9)]:
    DS = P_poly(S) - P_poly(RSET)
    ok, r1 = running_integral_positive(DS, 126)
    print(S, sign_pattern(DS), "R_126(y)>0 for all y:", ok, float(r1))
