#!/usr/bin/env python3
"""Numerical illustration of the next-prime sandwich and open problem 3.

Floating-point evidence, not a certificate. With J_n = I_{p_n} and q = p_{n+1}
(the least prime exceeding N = p_n),

    J_n - Lambda = sum_{k>n} K_k,   K_k = int_0^1 x^{p_k} prod_{r<p_k} (1 - x^r) dx.

The script computes -log(J_n - Lambda) in log space, the Laplace values
M_N = min_t [N t + Phi(t)] and M_q, and compares -log(J_n - Lambda) - M_q with
the heuristic  1/4 log q + 3/4 log log q - 1/2 log pi + 1/4 log(2 zeta(2)).

Requires numpy and sympy. Runtime: a few seconds.
"""
import numpy as np
from sympy import primerange

PMAX = 120000         # primes used for the tail terms K_k
PHI_PMAX = 600000     # primes used for Phi (far beyond the saddle point)

P = np.array(list(primerange(2, PMAX)), dtype=float)
u = np.linspace(np.log(1e-7), np.log(5.0), 12000)
t = np.exp(u)                     # x = e^{-t}, dx = t e^{-t} du
trapezoid = getattr(np, "trapezoid", None) or np.trapz

logs = np.zeros_like(t)           # log prod_{r < p_k} (1 - e^{-rt})
logK = np.empty(len(P))
for k, p in enumerate(P):
    f = -(p + 1) * t + logs + u
    m = f.max()
    logK[k] = m + np.log(trapezoid(np.exp(f - m), u))
    logs += np.log1p(-np.exp(-p * t))

PP = np.array(list(primerange(2, PHI_PMAX)), dtype=float)
ts = np.exp(np.linspace(np.log(3e-5), np.log(0.5), 3000))
PhiTs = np.array([-np.log1p(-np.exp(-PP * s)).sum() for s in ts])


def M(N):
    return (N * ts + PhiTs).min()


C0 = -0.5 * np.log(np.pi) + 0.25 * np.log(2 * np.pi ** 2 / 6)
index = {int(p): i for i, p in enumerate(P)}
ns = sorted(set(list(range(20, 9001, 97)) + [index[19609] + 1, index[31397] + 1]))

print(f"{'N':>7} {'gap':>4} {'-log(J-L)':>10} {'M_N':>9} {'M_q':>9} "
      f"{'-M_N':>6} {'-M_q':>6} {'resid':>7}")
res = []
for n in ns:
    N, q = P[n - 1], P[n]
    tail = logK[n:]
    m = tail.max()
    meas = -(m + np.log(np.exp(tail - m).sum()))
    MN, Mq = M(N), M(q)
    L = np.log(q)
    r = meas - Mq - (0.25 * L + 0.75 * np.log(L) + C0)
    res.append(r)
    if n % 970 == 20 or q - N >= 50:
        print(f"{int(N):7d} {int(q - N):4d} {meas:10.2f} {MN:9.2f} {Mq:9.2f} "
              f"{meas - MN:6.2f} {meas - Mq:6.2f} {r:7.3f}")
print(f"residual range over {len(ns)} values of n: [{min(res):.3f}, {max(res):.3f}]")
