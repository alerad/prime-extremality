#!/usr/bin/env python3
"""Counterexample search (floating point; evidence only).

For a primitive A in [2,N] the threshold is
   k*(A,N) = inf{ k : min_{0<y<=1} int_0^y k u^(k-1) (P_A - P_{P_N}) du < 0 },
i.e. ALL truncation levels c are included (not only c = 1).  Mode 'exhaustive': every maximal
primitive A in [2,N] (non-maximal sets are dominated), N in [NLO, NHI].
"""
import json, os, sys, time
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rv_common import maximal_antichains, is_prime, progress

HERE = os.path.dirname(os.path.abspath(__file__))
U = np.unique(np.concatenate([np.linspace(0.15, 0.85, 2500), np.linspace(0.85, 1.0, 14000)]))
U = U[U < 1.0]                       # u = 1 contributes D(1) = 0; append below
LOGU = np.log(U)
DU = np.diff(np.append(U, 1.0))
NMAX = 1200
LG = np.log1p(-np.power.outer(U, np.arange(1, NMAX + 1)).T)      # LG[n-1] = log(1 - u^n)
KCOARSE = np.array([60, 90, 110, 120, 125.0, 125.84, 127, 130, 135, 140, 150, 175, 200, 250, 300, 400])


def running_min(D, k):
    """min over grid y of int_0^y k u^(k-1) D (trapezoid; D(1)=0 appended), relative to scale."""
    w = np.exp(np.log(k) + (k - 1) * LOGU)
    f = D * w
    f1 = np.concatenate([f, np.zeros((f.shape[0], 1))], axis=1)
    cum = np.cumsum((f1[:, 1:] + f1[:, :-1]) / 2 * DU, axis=1)
    scale = np.cumsum(np.abs(f1[:, 1:]) * DU, axis=1)[:, -1]
    return cum.min(axis=1) / scale, cum[:, -1] / scale


def thresholds(D, tol=1e-10, c1_only=False):
    """vectorized: coarse scan then bisection, returns k* per row (inf if > 400)."""
    n = D.shape[0]
    first_fail = np.full(n, np.inf)
    last_ok = np.zeros(n)
    for k in KCOARSE:
        mn, end = running_min(D, k)
        v = end if c1_only else mn
        bad = (v < -tol) & np.isinf(first_fail)
        first_fail[bad] = k
        okm = (v >= -tol) & np.isinf(first_fail)
        last_ok[okm] = k
    idx = np.where(np.isfinite(first_fail))[0]
    lo, hi = last_ok[idx].copy(), first_fail[idx].copy()
    for _ in range(30):
        if len(idx) == 0:
            break
        mid = (lo + hi) / 2
        # per-row k: compute row-wise
        w = np.exp(np.log(mid)[:, None] + (mid - 1)[:, None] * LOGU[None, :])
        f = D[idx] * w
        f1 = np.concatenate([f, np.zeros((f.shape[0], 1))], axis=1)
        cum = np.cumsum((f1[:, 1:] + f1[:, :-1]) / 2 * DU, axis=1)
        scale = np.cumsum(np.abs(f1[:, 1:]) * DU, axis=1)[:, -1]
        v = (cum[:, -1] if c1_only else cum.min(axis=1)) / scale
        ok = v >= -tol
        lo = np.where(ok, mid, lo)
        hi = np.where(ok, hi, mid)
    out = np.full(n, np.inf)
    out[idx] = (lo + hi) / 2
    return out


def D_matrix(sets, N):
    PN = [q for q in range(2, N + 1) if is_prime(q)]
    LPN = LG[np.array(PN) - 1].sum(axis=0)
    ind = np.zeros((len(sets), N))
    for i, A in enumerate(sets):
        ind[i, np.array(A) - 1] = 1.0
    with np.errstate(all="ignore"):
        LA = ind @ LG[:N]
    assert np.all(np.isfinite(LA)), "non-finite log-products"
    return np.exp(LPN)[None, :] * np.expm1(LA - LPN[None, :])


K9 = 125.8404540694456574832


def run_N(N):
    """Stage A: every maximal primitive A in [2,N] evaluated at k = k_9 - 1e-6 and k = 140 (all y).
    Stage B: exact-ish threshold (bisection) only for sets failing at k = 140."""
    sets = maximal_antichains(list(range(2, N + 1)))
    PN = tuple(q for q in range(2, N + 1) if is_prime(q))
    sets = [A for A in sets if tuple(A) != PN]
    viol, near = [], []
    min_at_k9 = (np.inf, None)
    for s in range(0, len(sets), 2000):
        batch = sets[s:s + 2000]
        D = D_matrix(batch, N)
        m9, e9 = running_min(D, K9 - 1e-6)
        m140, _ = running_min(D, 140.0)
        for i, A in enumerate(batch):
            if m9[i] < min_at_k9[0]:
                min_at_k9 = (float(m9[i]), A)
            if m9[i] < -1e-10:
                viol.append((A, float(m9[i])))
        idx = np.where(m140 < -1e-10)[0]
        if len(idx):
            ks = thresholds(D[idx])
            kc = thresholds(D[idx], c1_only=True)
            for j, i in enumerate(idx):
                near.append((float(ks[j]), float(kc[j]), batch[i]))
    near.sort()
    return {"N": N, "nsets": len(sets), "violations": viol, "min_rel_running_at_k9": min_at_k9,
            "n_fail_140": len(near), "lowest": near[:3]}


if __name__ == "__main__":
    from multiprocessing import Pool
    NLO, NHI = int(sys.argv[1]), int(sys.argv[2])
    Ns = list(range(NHI, NLO - 1, -1))
    res = []
    with Pool(int(os.environ.get("JOBS", 12))) as pool:
        for i, r in enumerate(pool.imap_unordered(run_N, Ns)):
            res.append(r)
            print(json.dumps(r), flush=True)
            progress(i + 1, len(Ns), "exhaustive", "N")
    res.sort(key=lambda r: r["N"])
    with open(os.path.join(HERE, f"rv_cex_exhaustive_{NLO}_{NHI}.json"), "w") as f:
        json.dump(res, f, indent=1)
    print("total sets:", sum(r["nsets"] for r in res), " violations:", sum(len(r["violations"]) for r in res))
    for r in res:
        lw = r["lowest"][0] if r["lowest"] else None
        print(r["N"], r["nsets"], "fail@140:", r["n_fail_140"], "lowest k*(all c), k*(c=1), A:", lw,
              "| viol:", r["violations"][:2])
