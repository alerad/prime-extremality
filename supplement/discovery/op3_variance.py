#!/usr/bin/env python3
"""Fluctuations of the local factor  X_q = log(t_q log q * Sigma_q),  Sigma_q = sum_{p>=q} e^{-(p-q)t_q},
over primes q in ranges, vs. two models for primes near x (heuristic, not proofs):
  Cramer (independent, density 1/log x):  Var(X) ~ (t/2) log q
  Hardy-Littlewood pair correlations:     Var(X) ~ (t/2) [log q + 2 sum_{h>=1} (S(h)-1) e^{-h t}]
where S(h) is the singular series (S(h) = 0 for odd h).  Also the conditional mean given q prime:
  E[t log q Sigma_q] ~ t log q + t sum_{h>=1} S(h) e^{-h t}."""
import numpy as np
from sympy import primerange, factorint
d = np.load("op3_data.npz"); P, tp = d["P"], d["tp"]
C2 = 0.6601618158468696
H = 40000
Sh = np.zeros(H + 1)
for h in range(2, H + 1, 2):
    s = 2*C2
    for p in factorint(h):
        if p > 2:
            s *= (p - 1)/(p - 2)
    Sh[h] = s
X = []
for n in range(len(P)):
    q = P[n]
    if q < 2000 or q > 100000: continue
    Sig = np.exp(-(P[n:] - q)*tp[n]).sum()
    X.append((q, np.log(tp[n]*np.log(q)*Sig), tp[n]))
X = np.array(X)
hs = np.arange(1, H + 1)
print(f"{'q range':>16} {'#':>6} {'emp mean':>9} {'HL mean':>8} {'emp sd':>7} {'Cramer sd':>9} {'HL sd':>7}")
for lo, hi in ((2000, 5000), (5000, 10000), (10000, 20000), (20000, 40000), (40000, 70000), (70000, 100000)):
    m = (X[:, 0] >= lo) & (X[:, 0] < hi)
    qm = np.exp(np.log(X[m, 0]).mean()); t = X[m, 2].mean(); Lq = np.log(qm)
    w = np.exp(-hs*t)
    cram = np.sqrt(t/2*Lq)
    hl = np.sqrt(max(t/2*(Lq + 2*((Sh[1:] - 1)*w).sum()), 0))
    hl_mean = np.log(t*Lq + t*(Sh[1:]*w).sum())     # log of conditional mean (q prime included as the 1)
    print(f"{lo:>7}-{hi:<8} {m.sum():6d} {X[m,1].mean():+9.4f} {hl_mean:+8.4f} {X[m,1].std():7.4f} {cram:9.4f} {hl:7.4f}")
