#!/usr/bin/env python3
"""Referee follow-up: (i) correlation of the heuristic residual with -log(t_q log q Sigma_q) on other
N-ranges; (ii) Thm 2.4 residual minus t_q (the e^{-t} Jacobian factor that the main term omits)."""
import math, numpy as np
from r_op3 import PR, saddle, Sigma, a
d = np.load("r_op3_data.npz")
ps, logd = d["ps"], d["logd"]
logT = np.logaddexp.accumulate(logd[::-1])[::-1]
idx = {int(p): i for i, p in enumerate(ps)}
C0 = -0.5 * math.log(math.pi) + 0.25 * math.log(2 * a)
Ns = PR[(PR >= 1009) & (PR <= 100000)][::7]          # every 7th prime N (subsample), saddle per q
rows = []
for N in Ns:
    q = int(PR[np.searchsorted(PR, N, side="right")])
    tq, Mq, d2 = saddle(q)
    S = Sigma(q, tq)
    meas = -logT[idx[q]]
    main = Mq + 0.5 * math.log(d2 / (2 * math.pi)) - math.log(S)
    heur = Mq + 0.25 * math.log(q) + 0.75 * math.log(math.log(q)) + C0
    loc = -math.log(tq * math.log(q) * S)
    rows.append((N, q, tq, meas - main, meas - heur, loc))
R = np.array(rows)
for lo in (5000, 20000):
    m = R[:, 0] > lo
    print(f"N>{lo} (every 7th prime): corr(heur residual, -log(t_q log q Sigma_q)) = {np.corrcoef(R[m,5], R[m,4])[0,1]:.5f}, "
          f"slope = {np.polyfit(R[m,5], R[m,4], 1)[0]:.4f}")
for N in (1009, 10007, 31397, 99989):
    q = int(PR[np.searchsorted(PR, N, side="right")]); tq, Mq, d2 = saddle(q); S = Sigma(q, tq)
    res = -logT[idx[q]] - (Mq + 0.5 * math.log(d2 / (2 * math.pi)) - math.log(S))
    print(f"N={N}: Thm 2.4 residual {res:+.5f}, t_q = {tq:.5f}, residual - t_q = {res - tq:+.5f}")
m = R[:, 0] > 20000
print(f"N>20000: max |Thm2.4 residual - t_q| = {np.max(np.abs(R[m,3] - R[m,2])):.5f}")
