#!/usr/bin/env python3
"""Independent rigorous verification of the TAIL conditions of Proposition prop:cert by interval
arithmetic (float64 with outward rounding through np.nextafter; exact dyadic prefix sums).

Envelope integrand at K = 126 (k <= 126 then follows from [P, Lemma 3.1] with the nonincreasing
singular weight (k/K) u^(k-K), since the integrand is continuous on [0,1]):
  merged tail (R', A0):  g = K u^(K-1) P_{R0}(u) prod_{11<=q<=64}(1-u^q) [E(u) - P_{R'}(u)],
      E(u) = P_{A0}(u) prod_{n in C(A0)} (1-u^n)          (notes' envelope, mode 'notes'), or
      E(u) = P_{M}(u) prod_{n >= 120}(1-u^n), M = A0 + {n in C(A0): n < 120}   (code's, mode 'code')
  single tail (p, m_p, B_p, M):  g = K u^(K-1) prod_{q in Q}(1-u^q) [E(u^p) - (1-u^p)],
      E(v) = P_M(v) prod_{n >= B_p}(1-v^n),  Q = all primes in (p, p m_p].
Claim checked: G(y) = int_0^y g > 0 for all y in (0,1].
Method: (1) on (0,u0] g > 0 by Weierstrass/Bonferroni lower bounds checked in exact rationals
(psi decreasing); (2) on [u0,1] a uniform grid; on each cell [a,b] every factor is monotone, so
g >= g_lo(cell) from endpoint enclosures; G(y) >= sum_{previous cells} (b-a) g_lo + min(0,(b-a) g_lo).
"""
import json, os, sys, time, itertools
from fractions import Fraction as Fr
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rv_common import smooth_list, is_prime, primes_open_closed, RSET, progress

HERE = os.path.dirname(os.path.abspath(__file__))
K = 126
nd = np.nextafter
INF = np.inf
np.seterr(divide="ignore", invalid="ignore", over="ignore", under="ignore")


def mul(alo, ahi, blo, bhi):           # nonnegative intervals
    return np.maximum(nd(alo * blo, -INF), 0.0), nd(ahi * bhi, INF)


def one_minus(lo, hi):                 # 1 - x for x in [lo,hi] subset [0,1]
    return np.maximum(nd(1.0 - hi, -INF), 0.0), np.minimum(nd(1.0 - lo, INF), 1.0)


def pow_iv(lo, hi, n):
    rlo = rhi = None
    blo, bhi = lo.copy(), hi.copy()
    while n:
        if n & 1:
            if rlo is None:
                rlo, rhi = blo.copy(), bhi.copy()
            else:
                rlo, rhi = mul(rlo, rhi, blo, bhi)
        n >>= 1
        if n:
            blo, bhi = mul(blo, bhi, blo, bhi)
    return rlo, rhi


def prod_one_minus_powers(xlo, xhi, exps, nmax_extra=None):
    """enclosure of prod_{e in exps} (1 - x^e) for finite exps (incremental powers)."""
    exps = sorted(set(exps))
    plo = np.ones_like(xlo); phi = np.ones_like(xhi)
    if not exps:
        return plo, phi
    want = set(exps)
    clo, chi = xlo.copy(), xhi.copy()        # x^1
    for n in range(1, exps[-1] + 1):
        if n > 1:
            clo, chi = mul(clo, chi, xlo, xhi)
        if n in want:
            flo, fhi = one_minus(clo, chi)
            plo, phi = mul(plo, phi, flo, fhi)
    return plo, phi


def envelope(xlo, xhi, fin, inf_set_upto, N3, all_from=None):
    """enclosure of E(x) = prod_{n in fin}(1-x^n) * prod_{n in INF}(1-x^n), where INF is either
    {n >= all_from} (if all_from is given) or the given sorted list inf_set_upto (all elements of the
    infinite set that are <= N3); remainder bound prod_{n in INF, n > N3} >= 1 - x^(N3+1)/(1-x)."""
    if all_from is not None:
        want = set(fin) | set(range(all_from, N3 + 1))
    else:
        want = set(fin) | set(n for n in inf_set_upto if n <= N3)
    plo = np.ones_like(xlo); phi = np.ones_like(xhi)
    small = np.zeros_like(xlo)                            # upper bound of sum of tiny x^n (Weierstrass)
    THR = 2.0 ** -30
    clo, chi = xlo.copy(), xhi.copy()
    top = max(want) if want else 1
    for n in range(1, max(top, N3) + 2):
        if n > 1:
            clo, chi = mul(clo, chi, xlo, xhi)
        if n in want:
            tiny = chi < THR
            flo, fhi = one_minus(clo, chi)
            flo = np.where(tiny, 1.0, flo)               # tiny factors handled by 1 - sum
            plo, _ = mul(plo, plo, flo, flo)
            _, phi = mul(phi, phi, fhi, fhi)
            small = np.where(tiny, nd(small + chi, INF), small)
        if n == N3 + 1:
            pN1lo, pN1hi = clo, chi                       # x^(N3+1)
    omlo, omhi = one_minus(xlo, xhi)                      # 1 - x
    ratio_hi = nd(pN1hi / omlo, INF)                      # upper bound of x^(N3+1)/(1-x)
    ratio_hi = np.where(omlo > 0, ratio_hi, INF)
    tail_lo = np.maximum(nd(1.0 - nd(ratio_hi + small, INF), -INF), 0.0)
    Elo, _ = mul(plo, plo, tail_lo, tail_lo)
    return Elo, phi


def exact_prefix_check(lb):
    """lb: float lower bounds of int over cells.  Exact dyadic prefix sums.
    Returns (ok, min_i [prefix_i + min(0, lb_i)], total) as floats (from exact values)."""
    D = 1 << 1100
    vals = []
    for f in lb.tolist():
        n, d = float(f).as_integer_ratio()
        vals.append(n * (D // d))
    pref = 0
    worst = None
    for v in vals:
        cand = pref + min(0, v)
        if worst is None or cand < worst:
            worst = cand
        pref += v
    return worst >= 0, worst / D, pref / D


def near_zero_u0(kind, data):
    """largest u0 in a list with psi(u0) > 0 (exact rationals); psi decreasing."""
    for u0 in [Fr(n, 100) for n in range(99, 4, -1)]:
        if kind == "merged":
            Rp, A0, C_upto = data
            r0 = min(Rp)
            s = sum(u0 ** (r + t - r0) for r, t in itertools.combinations(Rp, 2))
            s += sum(u0 ** (a - r0) for a in A0)
            s += u0 ** (24 - r0) / (1 - u0)                       # sum_{n in C} u^n <= u^24/(1-u)
            assert all(a > r0 for a in A0)
        else:
            p, M, B = data
            v0 = u0 ** p
            s = sum(v0 ** (m - 1) for m in M) + v0 ** (B - 1) / (1 - v0)
        if 1 - s > 0:
            return u0
    return None


def check_case(task, NCELL=1 << 17, mode="notes"):
    kind = task[0]
    t0 = time.time()
    if kind == "merged":
        Rp, A0 = tuple(task[1]), tuple(task[2])
        R0 = [r for r in RSET if r not in Rp]
        C = [n for n in smooth_list(Rp, 24, 4000) if not is_prime(n) and not any(n % a == 0 for a in A0)]
        if not any(n >= 64 for n in C):
            return {"task": task, "ok": True, "type": "vacuous"}
        u0 = near_zero_u0("merged", (Rp, A0, C))
        Wexps = R0 + [q for q in range(11, 65) if is_prime(q)]
        Texps = list(Rp)
    else:
        p, mp, B, M = task[1], task[2], task[3], tuple(task[4])
        u0 = near_zero_u0("single", (p, M, B))
        Wexps = primes_open_closed(p, p * mp)
        Texps = [p]
    if u0 is None:
        return {"task": task, "ok": False, "reason": "no u0"}
    u = np.linspace(float(u0), 1.0, NCELL + 1)
    if Fr(float(u[0])) > u0:                        # first grid point must not exceed u0
        u[0] = np.nextafter(u[0], 0.0)
    assert Fr(float(u[0])) <= u0 and np.all(np.diff(u) > 0) and u[-1] == 1.0
    ulo, uhi = u.copy(), u.copy()
    # K u^(K-1)
    w1lo, w1hi = pow_iv(ulo, uhi, K - 1)
    w1lo, w1hi = np.maximum(nd(w1lo * K, -INF), 0), nd(w1hi * K, INF)
    Wlo, Whi = prod_one_minus_powers(ulo, uhi, Wexps)
    if kind == "merged":
        Tlo, Thi = prod_one_minus_powers(ulo, uhi, Texps)
        if mode == "notes":
            Elo, Ehi = envelope(ulo, uhi, A0, C, N3=3000)
        else:
            Mc = list(A0) + [n for n in C if n < 120]
            Elo, Ehi = envelope(ulo, uhi, Mc, None, N3=3000, all_from=120)
    else:
        vlo, vhi = pow_iv(ulo, uhi, p)
        Elo, Ehi = envelope(vlo, vhi, M, None, N3=1500, all_from=B)
        Tlo, Thi = one_minus(vlo, vhi)
    # cells [a,b] = [u_i, u_{i+1}]
    a, b = slice(0, NCELL), slice(1, NCELL + 1)
    poslo, poshi = mul(w1lo[a], w1hi[b], Wlo[b], Whi[a])          # w1 increasing, W decreasing
    dlo = nd(Elo[b] - Thi[a], -INF)                                # E, T decreasing
    glo = np.where(dlo >= 0, nd(poslo * dlo, -INF), nd(poshi * dlo, -INF))
    width = u[b] - u[a]                                            # exact (Sterbenz)
    lb = nd(width * glo, -INF)
    ok, worst, total = exact_prefix_check(lb)
    return {"task": task, "ok": bool(ok), "type": "IA", "u0": str(u0), "Glo_1": total,
            "min_lower": worst, "cells": NCELL, "t": round(time.time() - t0, 2)}


def main():
    from multiprocessing import Pool
    mode = os.environ.get("MODE", "notes")
    which = os.environ.get("WHICH", "all")
    ncell = int(os.environ.get("NCELL", 1 << 17))
    cases = json.load(open(os.path.join(HERE, "rv_cases.json")))
    tasks = []
    if which in ("all", "merged"):
        tasks += [("merged", Rp, A0) for Rp, A0 in cases["merged_tail"]]
    if which in ("all", "single"):
        tasks += [("single", p, mp, B, M) for p, mp, B, M in cases["single_tail"]]
    print(f"mode={mode} tasks={len(tasks)} cells={ncell}", flush=True)
    res = []
    t0 = time.time()
    from functools import partial
    with Pool(16) as pool:
        for i, r in enumerate(pool.imap_unordered(partial(check_case, NCELL=ncell, mode=mode), tasks, chunksize=1)):
            res.append(r)
            if not r["ok"]:
                print("FAIL:", r, flush=True)
            progress(i + 1, len(tasks), f"tails-{mode}", "case")
    out = os.path.join(HERE, f"rv_tails_{mode}_{which}.jsonl")
    with open(out, "w") as f:
        for r in res:
            f.write(json.dumps(r) + "\n")
    from collections import Counter
    print(f"done in {time.time() - t0:.0f}s;", dict(Counter((r['task'][0], r.get('type'), r['ok']) for r in res)))
    for kd in ("merged", "single"):
        rs = [r for r in res if r["task"][0] == kd and r.get("type") == "IA"]
        if rs:
            m = min(rs, key=lambda r: r["Glo_1"])
            print(f"  {kd}: min rigorous lower bound of G(1) = {m['Glo_1']:.3e} at {m['task']};"
                  f" min over y of lower bound = {min(r['min_lower'] for r in rs):.3e}")


if __name__ == "__main__":
    main()
