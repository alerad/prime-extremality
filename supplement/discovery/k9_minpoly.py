#!/usr/bin/env python3
"""Exact minimal polynomial of k_9: root of sum_n c_n k/(k+n) = 0, c_n = coeffs of P_{4,5,6,7,9} - P_{2,3,5,7}."""
import sympy as sp
k, u = sp.symbols('k u')
PA = sp.expand(sp.prod([1 - u**a for a in (4, 5, 6, 7, 9)]))
PP = sp.expand(sp.prod([1 - u**a for a in (2, 3, 5, 7)]))
D = sp.Poly(PA - PP, u)
f = sum(c * k / (k + n) for (n,), c in D.terms())
num = sp.factor(sp.numer(sp.together(f)))
print("numerator factored:", num)
num_poly = sp.Poly(sp.numer(sp.together(f)), k)
facs = sp.factor_list(num_poly)[1]
for fac, mult in facs:
    roots = [r for r in sp.Poly(fac, k).real_roots() if r > 1]
    for r in roots:
        val = sp.N(r, 40)
        if abs(val - sp.Float('125.84045406944565748', 40)) < 1e-10:
            print("minimal polynomial degree", sp.degree(fac, k))
            print("minimal polynomial:", sp.Poly(fac, k).as_expr())
            print("k_9 =", sp.N(r, 60))
            print("irreducible over Q:", sp.Poly(fac, k).is_irreducible)
