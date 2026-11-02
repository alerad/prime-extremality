#!/usr/bin/env python3
"""Structured competitors A = (P_N \\ R_r) u {pq <= N : p<=q in R_r}, R_r = first r primes.
For each r, crossing k (first k with E Z_A^k < E Z_P^k) at several N >= p_r^2. Evidence only."""
import numpy as np
from sympy import primerange, prime
from scipy.optimize import brentq
u, w = np.polynomial.laguerre.laggauss(80)
def f(A, P, k):
    X = np.exp(-u/k)
    lA = sum(np.log1p(-X**a) for a in A); lP = sum(np.log1p(-X**p) for p in P)
    return (np.exp(lA) - np.exp(lP)) @ w
def crossing(A, P):
    ks = np.arange(2, 3000, 1.0)
    for k0, k1 in zip(ks[:-1], ks[1:]):
        if f(A, P, k1) < 0:
            return brentq(lambda k: f(A, P, k), k0, k1)
    return None
for r in range(2, 9):
    R = list(primerange(2, prime(r)+1))
    out = []
    for N in sorted(set([R[-1]**2, R[-1]**2 + 1, R[-1]**2 + 10, 2*R[-1]**2])):
        P = list(primerange(2, N+1))
        S = sorted({p*q for i, p in enumerate(R) for q in R[i:] if p*q <= N})
        A = sorted(set(P) - set(R) | set(S))
        c = crossing(A, P)
        out.append(f"N={N}: k*={c:.3f}" if c else f"N={N}: none<3000")
    print(f"r={r} R={R}: " + ";  ".join(out), flush=True)
