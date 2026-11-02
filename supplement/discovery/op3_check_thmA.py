import numpy as np
d = np.load("op3_data.npz"); P, logD, tp, Mp, phi2 = d["P"], d["logD"], d["tp"], d["Mp"], d["phi2"]
R = np.load("op3_rows.npy")
idx = {int(p): i for i, p in enumerate(P)}
res = []
for row in R:
    N, q, meas = int(row[0]), int(row[1]), row[2]
    n = idx[q]
    Sig = np.exp(-(P[n:] - q)*tp[n]).sum()
    thmA = Mp[n] + 0.5*np.log(phi2[n]/(2*np.pi)) - np.log(Sig)   # -log of Theorem A main term
    res.append((N, meas - thmA, np.log(phi2[n]*tp[n]/(2*q)), np.log(tp[n]*np.sqrt(q*np.log(q)/(2*np.pi**2/6)))))
res = np.array(res)
for lo, hi in ((100, 1000), (1000, 10000), (10000, 50000), (50000, 100000)):
    m = (res[:,0] >= lo) & (res[:,0] < hi)
    print(f"N in [{lo},{hi}): Thm A residual in [{res[m,1].min():+.5f}, {res[m,1].max():+.5f}];"
          f"  log(Phi''t/2q) ~ {res[m,2].mean():+.4f};  log(t_q/sqrt(2a/(q log q))) ~ {res[m,3].mean():+.4f}")
