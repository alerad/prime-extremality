#!/usr/bin/env python3
"""Tables/figure data for the OP3 section (from op3_local.py output files)."""
import numpy as np
d = np.load("op3_data.npz"); P, logD, tp, Mp, phi2 = d["P"], d["logD"], d["tp"], d["Mp"], d["phi2"]
R = np.load("op3_rows.npy")
idx = {int(p): i for i, p in enumerate(P)}
a = np.pi**2/6; C0 = -0.5*np.log(np.pi) + 0.25*np.log(2*a)
rows = []
for row in R:
    N, q, meas = int(row[0]), int(row[1]), row[2]
    n = idx[q]; L = np.log(q)
    Sig = np.exp(-(P[n:] - q)*tp[n]).sum()
    heur = Mp[n] + 0.25*L + 0.75*np.log(L) + C0
    thmA = Mp[n] + tp[n] + 0.5*np.log(phi2[n]/(2*np.pi)) - np.log(Sig)   # main term with e^{-M_q - t_q}
    loc = np.log(tp[n]*L*Sig)
    rows.append((N, q - N, meas, meas - heur, meas - thmA, loc))
rows = np.array(rows)
# figure data: every 3rd point
with open("op3_residuals.dat", "w") as f:
    f.write("N heur thmA local\n")
    for r in rows[::3]:
        f.write(f"{int(r[0])} {r[3]:.5f} {r[4]:.5f} {r[5]:.5f}\n")
# full table for reproducibility
np.savetxt("op3_residuals_full.tsv", rows, fmt=["%d", "%d", "%.6f", "%.6f", "%.6f", "%.6f"],
           delimiter="\t", header="N\tgap_after_N\tminus_log_tail\tresid_heuristic\tresid_thmA\tlog(t_q log q Sigma_q)")
big = rows[:, 0] > 20000
print("heuristic residual, N>20000: range", rows[big, 3].min(), rows[big, 3].max(), "sd", rows[big, 3].std())
print("Thm A residual, N>20000: range", rows[big, 4].min(), rows[big, 4].max())
print("corr(heur resid, -local) N>5000:", np.corrcoef(rows[rows[:,0]>5000, 3], -rows[rows[:,0]>5000, 5])[0, 1])
print("corr(heur resid, -local) N>20000:", np.corrcoef(rows[big, 3], -rows[big, 5])[0, 1])
# regression: heur residual = alpha + beta*(-local)
m = rows[:, 0] > 20000
beta, alpha = np.polyfit(-rows[m, 5], rows[m, 3], 1)
print("fit heur = alpha + beta*(-local): alpha=%.4f beta=%.4f" % (alpha, beta))
for N0 in (1009, 10007, 19609, 31397, 50021, 89689, 99989):
    i = int(np.argmin(abs(rows[:, 0] - N0)))
    r = rows[i]
    print(f"{int(r[0])} & {int(r[1])} & {r[2]:.3f} & {r[3]:+.3f} & {-r[5]:+.3f} & {r[4]:+.4f} \\\\")
