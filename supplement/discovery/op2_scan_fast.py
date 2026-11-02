#!/usr/bin/env python3
"""Faster, numerically stable OP2 scan: f_A(k) = int_0^1 k x^{k-1}(P_A - P_P) dx
= int_0^inf e^{-u} (P_A - P_P)(e^{-u/k}) du, Gauss-Laguerre (products evaluated directly,
no polynomial expansion, so no cancellation). Reports, per N, the smallest k in [2, KMAX]
at which some maximal primitive A in [2,N] has f_A(k) < 0. Evidence only."""
import sys, json, time
import numpy as np
from sympy import primerange

def progress(done, total=None, **f):
    print("ANVIL_PROGRESS " + json.dumps({"done": done, "total": total, **f}), flush=True)

KMAX = 400
ks = np.arange(2.0, KMAX + 1, 0.5)
u, w = np.polynomial.laguerre.laggauss(60)
X = np.exp(-np.outer(1.0/ks, u))           # shape (len(ks), nodes)
logX = np.log(X)

def logP(A):
    s = np.zeros_like(X)
    for a in A:
        s += np.log1p(-np.exp(a*logX))
    return s

def max_antichains(N):
    nums = list(range(2, N+1))
    res = []
    def rec(i, chosen):
        if i == len(nums):
            for n in nums:
                if n in chosen_set: continue
                if not any(n % a == 0 or a % n == 0 for a in chosen):
                    return
            res.append(tuple(chosen)); return
        n = nums[i]
        if not any(n % a == 0 for a in chosen):
            chosen.append(n); chosen_set.add(n); rec(i+1, chosen); chosen.pop(); chosen_set.discard(n)
        if any(n % a == 0 for a in chosen) or any(m % n == 0 for m in range(2*n, N+1, n)):
            rec(i+1, chosen)
    chosen_set = set()
    rec(0, [])
    return res

def crossing(A, PP):
    D = np.exp(logP(A)) - PP
    f = D @ w
    neg = np.nonzero(f < 0)[0]
    return ks[neg[0]] if len(neg) else None

N0, N1 = int(sys.argv[1]), int(sys.argv[2])
for N in range(N0, N1 + 1):
    t0 = time.time()
    P = tuple(primerange(2, N+1))
    PP = np.exp(logP(P))
    ants = max_antichains(N)
    best = None
    progress(0, len(ants), phase=f"N={N}", unit="antichain")
    for i, A in enumerate(ants):
        if A == P: continue
        c = crossing(A, PP)
        if c is not None and (best is None or c < best[0]):
            best = (c, A)
        if i % 2000 == 0:
            progress(i, len(ants), phase=f"N={N}", unit="antichain")
    msg = (f"first crossing k~{best[0]:.1f} by {best[1]}" if best else f"primes win for all k<={KMAX}")
    print(f"N={N:3d} #max={len(ants):8d} {msg}  ({time.time()-t0:.1f}s)", flush=True)
