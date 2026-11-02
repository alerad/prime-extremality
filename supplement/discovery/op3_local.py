#!/usr/bin/env python3
"""OP3 experiment: is the residual of the next-prime heuristic explained by the
local count of primes in a window of length 1/t_q after q?

Floating point, not a certificate.
  delta_p = int_0^1 x^p prod_{r<p}(1-x^r) dx            (exact telescoping terms)
  J_n - Lambda = sum_{k>n} delta_{p_k}
  M_N = min_t (N t + Phi(t)), t_N its minimiser, Phi(t) = -sum_p log(1-e^{-pt})
Predictions for -log(J_n - Lambda), q = p_{n+1}:
  A (paper heuristic): M_q + 1/4 log q + 3/4 loglog q - 1/2 log pi + 1/4 log(2 zeta 2)
  B (local window)   : M_q + 1/2 log(q/(pi t_q)) - log Sigma_q,  Sigma_q = sum_{p>=q} e^{-(p-q) t_q}
  C (sum of Laplace) : -log sum_{p>=q} sqrt(2 pi/Phi''(t_p)) exp(-M_p - t_p)
"""
import json, sys, time
import numpy as np
from sympy import primerange

def progress(done, total=None, **f):
    print("ANVIL_PROGRESS " + json.dumps({"done": done, "total": total, **f}), flush=True)

PMAX = 160000
PHI_PMAX = 700000
P = np.array(list(primerange(2, PMAX)), dtype=float)
PP = np.array(list(primerange(2, PHI_PMAX)), dtype=float)
a = np.pi**2/6

# ---- exact telescoping terms delta_p (log), trapezoid in u = log t
u = np.linspace(np.log(1e-7), np.log(6.0), 16000)
t = np.exp(u)
logs = np.zeros_like(t)
logD = np.empty(len(P))
trap = getattr(np, "trapezoid", None) or np.trapz
t0 = time.time()
progress(0, len(P), phase="delta_p", unit="prime")
for k, p in enumerate(P):
    f = -(p + 1) * t + logs + u
    m = f.max()
    logD[k] = m + np.log(trap(np.exp(f - m), u))
    logs += np.log1p(-np.exp(-p * t))
    if k % 1000 == 0:
        progress(k, len(P), phase="delta_p", unit="prime")
progress(len(P), len(P), phase="delta_p", unit="prime")

# ---- saddle quantities for each prime p: t_p, M_p, Phi''(t_p) via Newton
def phi_derivs(ts):
    out0 = np.zeros_like(ts); out1 = np.zeros_like(ts); out2 = np.zeros_like(ts)
    for chunk in np.array_split(PP, 40):
        e = np.exp(-np.outer(ts, chunk))        # e^{-pt}
        out0 += -np.log1p(-e).sum(1)
        r = e/(1-e)
        out1 += -(chunk*r).sum(1)               # Phi'
        out2 += (chunk**2*r/(1-e)).sum(1)       # Phi''
    return out0, out1, out2

tp = np.sqrt(2*a/(P*np.log(P)))                 # first-order guess
progress(0, 8, phase="newton", unit="iter")
for it in range(8):
    f0, f1, f2 = phi_derivs(tp)
    tp = tp - (f1 + P)/f2                         # solve Phi'(t) = -p
    tp = np.maximum(tp, 1e-9)
    progress(it+1, 8, phase="newton", unit="iter")
f0, f1, f2 = phi_derivs(tp)
Mp = P*tp + f0
np.savez("op3_data.npz", P=P, logD=logD, tp=tp, Mp=Mp, phi2=f2)

logLap = 0.5*np.log(2*np.pi/f2) - Mp - tp
ratio = logD - logLap
print("log(delta_p / Laplace) at p ~ 100, 1e3, 1e4, 1e5:",
      [round(float(ratio[np.searchsorted(P, x)]), 5) for x in (100, 1000, 10000, 100000)])

C0 = -0.5*np.log(np.pi) + 0.25*np.log(2*a)
rows = []
n_max = int(np.searchsorted(P, 100000))
for n in range(30, n_max):
    q = P[n]                                    # p_{n+1}, N = P[n-1]
    tail = logD[n:]; m = tail.max()
    meas = -(m + np.log(np.exp(tail - m).sum()))
    L = np.log(q)
    predA = Mp[n] + 0.25*L + 0.75*np.log(L) + C0
    Sig = np.exp(-(P[n:] - q)*tp[n]).sum()
    predB = Mp[n] + 0.5*np.log(q/(np.pi*tp[n])) - np.log(Sig)
    lc = logLap[n:]; mc = lc.max()
    predC = -(mc + np.log(np.exp(lc - mc).sum()))
    rows.append((P[n-1], q, meas, predA, predB, predC, np.log(tp[n]*L*Sig)))
R = np.array(rows)
np.save("op3_rows.npy", R)
rA = R[:, 2]-R[:, 3]; rB = R[:, 2]-R[:, 4]; rC = R[:, 2]-R[:, 5]
print(f"n range: N = {int(R[0,0])} .. {int(R[-1,0])}  ({len(R)} values)")
for name, r in (("A paper heuristic", rA), ("B local window", rB), ("C sum of Laplace", rC)):
    big = R[:, 0] > 20000
    print(f"{name:20s} all: [{r.min():+.4f}, {r.max():+.4f}]  N>20000: [{r[big].min():+.4f}, {r[big].max():+.4f}]  sd(N>20000)={r[big].std():.4f}")
corr = np.corrcoef(rA[R[:,0]>5000], -R[R[:,0]>5000, 6])[0, 1]
print("corr(residual A, -log(t_q log q Sigma_q)) for N>5000:", round(float(corr), 4))
for N0 in (19609, 31397, 89689):
    i = int(np.searchsorted(R[:, 0], N0))
    print(f"N={int(R[i,0])} gap={int(R[i,1]-R[i,0])}: meas={R[i,2]:.4f} A={R[i,3]:.4f} B={R[i,4]:.4f} C={R[i,5]:.4f}")
