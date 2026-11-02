#!/usr/bin/env python3
"""Corrected tail for the merged {2,3,5,7} step (floating point exploration).
S = R0 u S' with R0 = S cap {2,3,5,7}; S' is an antichain of composites in <R'>, R' = R \\ R0
(elements of S' are not divisible by any r in R0). Comparison integrand:
  P_{R0} * prod_{11<=q<=N}(1-u^q) * (P_{S'} - P_{R'}).
Tail (max S' >= MCUT): S'_small lies in a maximal antichain M of the composites of <R'> below B,
S'_large in the composites >= B: P_{S'} >= P_M * prod_{n composite in <R'>, n >= B}(1-u^n)."""
import sys, itertools
import numpy as np
from sympy import primerange
src = open("stage3_explore.py").read().split("R = (2, 3, 5, 7)")[0]
exec(src)
R = (2, 3, 5, 7)
MCUT = int(sys.argv[1]) if len(sys.argv) > 1 else 64
for B in (24, 36, 48):
    worst = (1e9, None, None)
    for r in range(1, 5):
        for Rp in itertools.combinations(R, r):
            R0 = tuple(x for x in R if x not in Rp)
            comps = [n for n in smooth(Rp, 4, 10**7) if n not in Rp]
            Ms = all_maximal_antichains([n for n in comps if n < B])
            big = prod_one_minus([n for n in comps if n >= B][:800], u)
            W = prod_one_minus(list(R0) + list(primerange(11, MCUT + 1)), u)
            PRp = prod_one_minus(Rp, u)
            for M in Ms:
                t = threshold(W * (prod_one_minus(M, u) * big - PRp))
                if t < worst[0]:
                    worst = (t, Rp, M)
    print(f"B={B}, weight primes [11,{MCUT}]: worst tail k* = {worst[0]:.2f} at R'={worst[1]}, M={worst[2]}", flush=True)
