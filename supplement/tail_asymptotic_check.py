#!/usr/bin/env python3
"""Numerical illustration of Theorem 5.4 (tail asymptotics of Lambda).

Floating-point evidence, not a certificate. With J_n = I_{p_n},

    J_n - Lambda = sum_{k>n} K_k,   K_k = int_0^1 x^{p_k} prod_{q<p_k} (1 - x^q) dx,

since adding the prime p_k to the set of smaller primes removes exactly K_k.
Each K_k is computed in log space with x = e^{-t} on a logarithmic t-grid, so
that tails as small as e^{-200} are resolved. The script prints
-log(J_n - Lambda) against the leading term (2 pi / sqrt 3) sqrt(n), the
N-form leading term 2 pi sqrt(N / (3 log N)) at N = p_n, and the Laplace value
min_t [N t + Phi(t)], Phi(t) = -log prod_p (1 - e^{-pt}).

Requires numpy and sympy. Runtime: a few seconds.
"""
import numpy as np
from sympy import primerange

PMAX = 80000          # primes used for the tail terms K_k
PHI_PMAX = 400000     # primes used for Phi (far beyond the saddle point)

P = np.array(list(primerange(2, PMAX)), dtype=float)
u = np.linspace(np.log(1e-7), np.log(5.0), 6000)
t = np.exp(u)                     # x = e^{-t}, dx = t e^{-t} du
trapezoid = getattr(np, "trapezoid", None) or np.trapz

logs = np.zeros_like(t)           # log prod_{q < p_k} (1 - e^{-qt})
logK = np.empty(len(P))
for k, p in enumerate(P):
    f = -(p + 1) * t + logs + u   # log of the integrand of K_k in the variable u
    m = f.max()
    logK[k] = m + np.log(trapezoid(np.exp(f - m), u))
    logs += np.log1p(-np.exp(-p * t))

Lam = 1 - np.exp(logK).sum()
print(f"1 - sum_k K_k = {Lam:.13f}   (Lambda = 0.5506530112728...)")

PP = np.array(list(primerange(2, PHI_PMAX)), dtype=float)


def Phi(ts):
    return np.array([-np.log1p(-np.exp(-PP * s)).sum() for s in ts])


ts = np.exp(np.linspace(np.log(1e-4), np.log(0.5), 800))
PhiTs = Phi(ts)
c = 2 * np.pi / np.sqrt(3)
print(f"2 pi / sqrt 3 = {c:.4f}")
print(f"{'n':>5} {'p_n':>6} {'-log(J_n-L)':>12} {'/sqrt n':>8} "
      f"{'2pi sqrt(N/3logN)':>18} {'min_t[Nt+Phi]':>14} {'diff':>6} {'log N':>6}")
for n in [30, 100, 300, 1000, 2000, 4000]:
    N = P[n - 1]                  # p_n (1-indexed: p_1 = 2)
    tail = logK[n:]               # K_k for primes p_k > p_n
    m = tail.max()
    meas = -(m + np.log(np.exp(tail - m).sum()))
    lead = 2 * np.pi * np.sqrt(N / (3 * np.log(N)))
    lap = (N * ts + PhiTs).min()
    print(f"{n:5d} {int(N):6d} {meas:12.2f} {meas / np.sqrt(n):8.4f} "
          f"{lead:18.2f} {lap:14.2f} {meas - lap:6.2f} {np.log(N):6.2f}")
