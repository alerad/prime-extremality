#!/usr/bin/env python3
"""Compatibility-aware tail for the merged {2,3,5,7} step (floating point exploration).
For S' (composites of <R'>, antichain, max S' >= MCUT) with small part A = S' cap [4,B):
  P_{S'} >= P_A * prod_{n composite of <R'>, n >= B, no a in A divides n} (1 - u^n),
and the tail is vacuous when no such n exists.  A ranges over ALL antichains of C cap [4,B)."""
import sys, itertools
import numpy as np
from sympy import primerange
exec(open("stage3_explore.py").read().split("R = (2, 3, 5, 7)")[0])
R = (2, 3, 5, 7)
MCUT = int(sys.argv[1]) if len(sys.argv) > 1 else 64

def all_antichains(Xf):
    res = []
    def rec(i, chosen):
        if i == len(Xf):
            res.append(tuple(chosen)); return
        x = Xf[i]
        if not any(x % a == 0 for a in chosen):
            rec(i + 1, chosen + [x])
        rec(i + 1, chosen)
    rec(0, [])
    return res

for B in (24, 30, 36):
    worst, count, vac = (1e9, None, None), 0, 0
    for r in range(1, 5):
        for Rp in itertools.combinations(R, r):
            R0 = [x for x in R if x not in Rp]
            comps = [n for n in smooth(Rp, 4, 10**6) if n not in Rp]
            small = [n for n in comps if n < B]
            large = [n for n in comps if n >= B]
            W = prod_one_minus(R0 + list(primerange(11, MCUT + 1)), u)
            PRp = prod_one_minus(Rp, u)
            for A in all_antichains(small):
                compat = [n for n in large if not any(n % a == 0 for a in A)]
                if not compat:
                    vac += 1; continue
                count += 1
                g = W * (prod_one_minus(A, u) * prod_one_minus(compat[:500], u) - PRp)
                t = threshold(g)
                if t < worst[0]:
                    worst = (t, Rp, A)
    print(f"B={B}: {count} small parts ({vac} vacuous), worst tail k* = {worst[0]:.2f} at R'={worst[1]}, A={worst[2]}", flush=True)
